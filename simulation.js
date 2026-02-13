// =======================================================
// TEN-T Flow Simulation + Leaflet Background Map
// Stable version: Map behind canvas, sidebar remains clickable
// =======================================================

console.log("simulation.js loaded (leaflet version)");

const canvas  = document.getElementById("network");
const ctx     = canvas.getContext("2d");
const tooltip = document.getElementById("tooltip");
const statsEl = document.getElementById("stats");

const btnToggle = document.getElementById("btn-toggle");
const btnReset  = document.getElementById("btn-reset");

const flowSlider = document.getElementById("flow-slider");
const flowValue  = document.getElementById("flow-value");

// --- safety checks
if (!canvas || !ctx || !btnToggle || !btnReset) {
    throw new Error("Missing DOM elements. Check simulation.html IDs.");
}
if (typeof L === "undefined") {
    throw new Error("Leaflet (L) not loaded. Check Leaflet <script> include in HTML.");
}

// ---------------- Leaflet Map ----------------
const map = L.map("map", {
    zoomControl: false,
    attributionControl: false,

    dragging: true,          // Leaflet übernimmt Pan
    scrollWheelZoom: true,   // Leaflet übernimmt Zoom
    doubleClickZoom: true,
    boxZoom: true,
    keyboard: true
}).setView([51.0, 10.0], 5);
const mapContainer = document.getElementById("map");
let overMapArea = false;

const mapArea = document.querySelector(".canvas-container");
mapArea.addEventListener("mouseenter", () => overMapArea = true);
mapArea.addEventListener("mouseleave", () => overMapArea = false);

// verhindert Seiten-Zoom (Ctrl + Wheel / Trackpad-Pinch)
mapContainer.addEventListener("wheel", (e) => {
    if (e.ctrlKey) e.preventDefault();
}, { passive: false });

// 👉 Zoom NUR wenn Maus über der Map (wie ten_t_map.html)


// 🔧 WICHTIG: Leaflet zwingen, die echte Größe zu berechnen
setTimeout(() => {
    map.invalidateSize();
}, 0);

L.tileLayer("https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png", {
    maxZoom: 19
}).addTo(map);


// ---------------- Canvas / DPR ----------------
let width = 0, height = 0, dpr = window.devicePixelRatio || 1;

function resizeCanvasToMap() {
    const size = map.getSize();
    width = size.x;
    height = size.y;
    dpr = window.devicePixelRatio || 1;

    canvas.width  = Math.round(width * dpr);
    canvas.height = Math.round(height * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
}

window.addEventListener("resize", () => {
    map.invalidateSize();
    resizeCanvasToMap();
    // speed depends on pixel length -> rebuild on size changes
    rebuildParticles();
});
// verhindert Browser-Zoom (Ctrl+Wheel/Trackpad-Pinch) – aber nur im Map Bereich
window.addEventListener("wheel", (e) => {
    if (!overMapArea) return;
    if (e.ctrlKey) e.preventDefault();
}, { passive: false });

// ---------------- Data ----------------
let NODES = [];
let EDGES_ORIG = [];
let EDGES_DYN = [];

let NODE_BY_ID = new Map();  // id -> node
let EDGE_STATE = new Map();  // key -> { blocked, flow, overloaded, kind, role }

let particles = [];
let running = false;
let timeMs = 0;

// ---------------- Settings ----------------
let FLOW_SCALE = 1.0; // slider sets this (0.3 .. 2.5)

// overload tuning / capacities
const CAP_FACTOR = 1.35; // 1.2–1.6
const MIN_CAP = 8;
let BASELINE_FLOW = new Map(); // key(orig) -> baseline flow

// dyn edges (optional support)
const MAX_NEAR_KM = 350;
const HUB_COUNT = 8;
const HUB_RADIUS = 600;

// costs
const ALT_EDGE_PENALTY_DYN = 1.35;
const ALT_EDGE_PENALTY_PRE = 1.12;

// visibility gate
let ALT_MODE = false;

// ORIGINAL edges used as reroute alternatives
let ALT_USED_ORIG = new Set();

// ---------------- Helpers ----------------
function node(id) { return NODE_BY_ID.get(Number(id)); }

function edgeKey(u, v, kind) {
    const a = Math.min(Number(u), Number(v));
    const b = Math.max(Number(u), Number(v));
    return `${a}-${b}-${kind}`;
}

function haversineKm(a, b) {
    const R = 6371;
    const toRad = deg => deg * Math.PI / 180;
    const dLat = toRad(b.lat - a.lat);
    const dLon = toRad(b.lon - a.lon);
    const la1 = toRad(a.lat), la2 = toRad(b.lat);
    const s = Math.sin(dLat/2)**2 + Math.cos(la1)*Math.cos(la2)*Math.sin(dLon/2)**2;
    return 2 * R * Math.asin(Math.sqrt(s));
}

function distancePointToSegment(px, py, x1, y1, x2, y2) {
    const dx = x2 - x1, dy = y2 - y1;
    if (dx === 0 && dy === 0) return Math.hypot(px - x1, py - y1);
    const t = ((px - x1) * dx + (py - y1) * dy) / (dx*dx + dy*dy);
    const clamped = Math.max(0, Math.min(1, t));
    const cx = x1 + clamped * dx;
    const cy = y1 + clamped * dy;
    return Math.hypot(px - cx, py - cy);
}

function logicalCapForKey(k) {
    const vals = [...BASELINE_FLOW.values()].filter(v => v > 0).sort((a,b)=>a-b);
    const median = vals.length ? vals[Math.floor(vals.length/2)] : MIN_CAP;

    const base = BASELINE_FLOW.get(k) || 0;
    const ref = (base > 0 ? base : median * 0.6);
    return Math.max(MIN_CAP, ref * CAP_FACTOR);
}

function hasAnyBlockedOrig() {
    for (const e of EDGES_ORIG) {
        const st = EDGE_STATE.get(edgeKey(e.von_id, e.zu_id, "orig"));
        if (st?.blocked) return true;
    }
    return false;
}
function hasAnyOverloadedOrig() {
    for (const e of EDGES_ORIG) {
        const st = EDGE_STATE.get(edgeKey(e.von_id, e.zu_id, "orig"));
        if (st?.overloaded && e.role === "main") return true;
    }
    return false;
}

// --- Leaflet projection: lat/lon -> canvas pixels
function nodeToCanvas(n) {
    const p = map.latLngToContainerPoint([n.lat, n.lon]);
    return { x: p.x, y: p.y };
}

// ---------------- Fit map to nodes ----------------
let userInteracted = false;

function fitMapToNodes() {
    if (!NODES.length) return;

    const lats = NODES.map(n => n.lat);
    const lons = NODES.map(n => n.lon);
    const minLat = Math.min(...lats), maxLat = Math.max(...lats);
    const minLon = Math.min(...lons), maxLon = Math.max(...lons);

    const bounds = L.latLngBounds(
        L.latLng(minLat, minLon),
        L.latLng(maxLat, maxLon)
    );

    map.fitBounds(bounds.pad(0.08), { animate: false });
    map.invalidateSize();
    resizeCanvasToMap();
    rebuildParticles();
}

// ---------------- Load network.json ----------------
async function loadNetwork() {
    const res = await fetch("network.json", { cache: "no-store" });
    if (!res.ok) throw new Error("network.json not found / not readable");
    const data = await res.json();

    NODES = data.nodes.map(n => ({
        ...n,
        id: Number(n.id),
        name: String(n.name || ""),
        land: String(n.land || ""),
        typ: String(n.typ || ""),
        lat: Number(n.lat),
        lon: Number(n.lon),
        einwohner: Number(n.einwohner) || 0,
        gueter_in: Number(n.gueter_in) || 0,
        gueter_out: Number(n.gueter_out) || 0
    }));

    EDGES_ORIG = data.edges.map(e => ({
        ...e,
        von_id: Number(e.von_id),
        zu_id: Number(e.zu_id),
        typ: String(e.typ || ""),
        distanz_km: Number(e.distanz_km) || 1,
        fracht_schaetzung: Number(e.fracht_schaetzung) || 0,
        kind: "orig",
        role: "main"
    }));

    // all original edges main (as in your current file)
    for (const e of EDGES_ORIG) e.role = "main";

    NODE_BY_ID = new Map(NODES.map(n => [n.id, n]));

    EDGE_STATE.clear();
    for (const e of EDGES_ORIG) {
        const k = edgeKey(e.von_id, e.zu_id, "orig");
        EDGE_STATE.set(k, { blocked:false, flow:0, overloaded:false, kind:"orig", role:e.role });
    }

    EDGES_DYN = [];
    ALT_USED_ORIG = new Set();

    fitMapToNodes();
}

// ---------------- Demands (OD) ----------------
function buildODDemands() {
    const sources = NODES.filter(n => n.gueter_out > 0);
    const sinks   = NODES.filter(n => n.gueter_in  > 0);

    const totalIn = sinks.reduce((s,n) => s + n.gueter_in, 0) || 1;
    const demands = [];

    for (const s of sources) {
        const out = s.gueter_out * FLOW_SCALE;
        for (const t of sinks) {
            if (s.id === t.id) continue;
            const share = t.gueter_in / totalIn;
            const amount = out * share;
            if (amount > 0.001) demands.push({ from: s.id, to: t.id, amount });
        }
    }
    return demands;
}

// ---------------- Dynamic edges (optional support) ----------------
function computeHubs() {
    const sorted = [...NODES].sort((a,b) => (b.einwohner||0) - (a.einwohner||0));
    return new Set(sorted.slice(0, HUB_COUNT).map(n => n.id));
}

function buildDynamicEdges() {
    const hubs = computeHubs();
    const dyn = [];

    for (let i=0; i<NODES.length; i++) {
        for (let j=i+1; j<NODES.length; j++) {
            const a = NODES[i], b = NODES[j];
            const km = haversineKm(a, b);
            if (km <= MAX_NEAR_KM) {
                dyn.push({ von_id:a.id, zu_id:b.id, typ:"alt_near", distanz_km:km, fracht_schaetzung: 30, kind:"dyn" });
            }
        }
    }

    const hubNodes = NODES.filter(n => hubs.has(n.id));
    for (const h of hubNodes) {
        for (const n of NODES) {
            if (h.id === n.id) continue;
            const km = haversineKm(h, n);
            if (km <= HUB_RADIUS) {
                dyn.push({ von_id:h.id, zu_id:n.id, typ:"alt_hub", distanz_km:km, fracht_schaetzung: 40, kind:"dyn" });
            }
        }
    }

    const origSet = new Set(EDGES_ORIG.map(e => edgeKey(e.von_id, e.zu_id, "orig")));
    const uniq = new Map();
    for (const e of dyn) {
        if (origSet.has(edgeKey(e.von_id, e.zu_id, "orig"))) continue;
        const k = edgeKey(e.von_id, e.zu_id, "dyn");
        if (!uniq.has(k)) uniq.set(k, e);
    }

    EDGES_DYN = [...uniq.values()];
    for (const e of EDGES_DYN) {
        const k = edgeKey(e.von_id, e.zu_id, "dyn");
        if (!EDGE_STATE.has(k)) EDGE_STATE.set(k, { blocked:false, flow:0, overloaded:false, kind:"dyn", role:"dyn" });
    }
}

// ---------------- Routing graph + Dijkstra ----------------
function buildAdj(mode, opts = {}) {
    const { ignoreBlocks = false } = opts;

    const adj = new Map();
    const add = (u, v, cost, kind) => {
        if (!adj.has(u)) adj.set(u, []);
        adj.get(u).push({ v, cost, kind });
    };

    let edges = [];
    if (mode === "main_only") {
        edges = EDGES_ORIG.filter(e => e.role === "main");
    } else {
        edges = [...EDGES_ORIG, ...EDGES_DYN];
    }

    for (const e of edges) {
        const u = e.von_id, v = e.zu_id;
        const kind = (e.kind === "dyn") ? "dyn" : "orig";

        const k = edgeKey(u, v, kind);
        const st = EDGE_STATE.get(k);
        if (!ignoreBlocks && st?.blocked) continue;

        let penalty = 1.0;
        if (kind === "dyn") penalty = ALT_EDGE_PENALTY_DYN;
        if (kind === "orig" && e.role === "alt_pre") penalty = ALT_EDGE_PENALTY_PRE;

        const cost = (Number(e.distanz_km) || 1) * penalty;

        add(u, v, cost, kind);
        add(v, u, cost, kind);
    }

    return adj;
}

function dijkstra(adj, start, goal) {
    const dist = new Map();
    const prev = new Map();
    const prevKind = new Map();
    const pq = [];

    dist.set(start, 0);
    pq.push({ n: start, d: 0 });

    while (pq.length) {
        pq.sort((a,b) => a.d - b.d);
        const { n, d } = pq.shift();
        if (n === goal) break;
        if (d !== dist.get(n)) continue;

        const neigh = adj.get(n) || [];
        for (const { v, cost, kind } of neigh) {
            const nd = d + cost;
            if (nd < (dist.get(v) ?? Infinity)) {
                dist.set(v, nd);
                prev.set(v, n);
                prevKind.set(v, kind);
                pq.push({ n: v, d: nd });
            }
        }
    }

    if (!dist.has(goal)) return null;

    const path = [];
    let cur = goal;
    while (cur !== start) {
        const p = prev.get(cur);
        if (p == null) break;
        path.push({ u: p, v: cur, kind: prevKind.get(cur) || "orig" });
        cur = p;
    }
    path.reverse();
    return path;
}

// ---------------- Flows / Overloads ----------------
function resetFlowsOnly() {
    for (const st of EDGE_STATE.values()) st.flow = 0;
}
function clearOverloadsOnly() {
    for (const st of EDGE_STATE.values()) st.overloaded = false;
}
function addFlowOnPath(path, amount) {
    if (!path) return;
    for (const seg of path) {
        const k = edgeKey(seg.u, seg.v, seg.kind);
        const st = EDGE_STATE.get(k);
        if (st) st.flow += amount;
    }
}
function markOverloads() {
    const baseVals = [...BASELINE_FLOW.values()].filter(v => v > 0).sort((a,b)=>a-b);
    const median = baseVals.length ? baseVals[Math.floor(baseVals.length/2)] : MIN_CAP;

    for (const [k, st] of EDGE_STATE.entries()) {
        const isOrig = k.endsWith("-orig");
        if (!isOrig) { st.overloaded = false; continue; }

        const base = BASELINE_FLOW.get(k) || 0;
        const cap = Math.max(MIN_CAP, (base > 0 ? base : median * 0.6) * CAP_FACTOR);
        st.overloaded = (st.flow > cap);
    }
}

// ---------------- Recalc ----------------
function recalc() {
    const demands = buildODDemands();

    // 0) Baseline: main-only, ignore blocks
    const adjBaseline = buildAdj("main_only", { ignoreBlocks: true });

    BASELINE_FLOW.clear();
    for (const d of demands) {
        const pBase = dijkstra(adjBaseline, d.from, d.to);
        if (!pBase) continue;
        for (const seg of pBase) {
            if (seg.kind !== "orig") continue;
            const k = edgeKey(seg.u, seg.v, "orig");
            BASELINE_FLOW.set(k, (BASELINE_FLOW.get(k) || 0) + d.amount);
        }
    }

    const basePaths = new Map();
    for (const d of demands) {
        basePaths.set(`${d.from}-${d.to}`, dijkstra(adjBaseline, d.from, d.to));
    }

    // 1) Pass 1: current main-only with blocks
    resetFlowsOnly();
    clearOverloadsOnly();

    const adjMain = buildAdj("main_only", { ignoreBlocks: false });
    const mainPathsNow = new Map();

    for (const d of demands) {
        const pNow = dijkstra(adjMain, d.from, d.to);
        mainPathsNow.set(`${d.from}-${d.to}`, pNow);
        if (pNow) addFlowOnPath(pNow, d.amount);
    }

    EDGES_DYN = [];
    markOverloads();

    const disrupted = new Set();
    for (const e of EDGES_ORIG) {
        const k = edgeKey(e.von_id, e.zu_id, "orig");
        const st = EDGE_STATE.get(k);
        if (!st) continue;
        if (st.blocked || (st.overloaded && e.role === "main")) disrupted.add(k);
    }

    ALT_MODE = hasAnyBlockedOrig() || hasAnyOverloadedOrig();

    // 2) dynamic edges only if needed
    if (ALT_MODE) buildDynamicEdges();
    else EDGES_DYN = [];

    // 3) Pass 2 final flows + mark reroute-orig delta
    resetFlowsOnly();
    clearOverloadsOnly();
    ALT_USED_ORIG = new Set();

    const adjAll = ALT_MODE ? buildAdj("with_alt", { ignoreBlocks: false }) : adjMain;

    for (const d of demands) {
        const base = basePaths.get(`${d.from}-${d.to}`);
        const pMain = mainPathsNow.get(`${d.from}-${d.to}`);

        let affected = false;
        if (!base) affected = true;
        else {
            for (const seg of base) {
                if (seg.kind !== "orig") continue;
                const k = edgeKey(seg.u, seg.v, "orig");
                if (disrupted.has(k)) { affected = true; break; }
            }
        }

        const pFinal = affected ? dijkstra(adjAll, d.from, d.to) : pMain;

        if (pFinal) {
            addFlowOnPath(pFinal, d.amount);

            if (ALT_MODE && affected && base) {
                const baseSet = new Set(base.filter(s => s.kind === "orig").map(s => edgeKey(s.u, s.v, "orig")));
                const baseSig = base.map(s => edgeKey(s.u, s.v, s.kind)).join("|");
                const newSig  = pFinal.map(s => edgeKey(s.u, s.v, s.kind)).join("|");

                if (baseSig !== newSig) {
                    for (const seg of pFinal) {
                        if (seg.kind !== "orig") continue;
                        const k = edgeKey(seg.u, seg.v, "orig");
                        if (!baseSet.has(k)) ALT_USED_ORIG.add(k);
                    }
                }
            }
        }
    }

    markOverloads();
    ALT_MODE = hasAnyBlockedOrig() || hasAnyOverloadedOrig();

    rebuildParticles();
    updateStats();
}

// ---------------- Particles ----------------
function rebuildParticles() {
    particles = [];

    const allEdges = [
        ...EDGES_ORIG.map(e => ({...e, kind:"orig"})),
        ...EDGES_DYN.map(e => ({...e, kind:"dyn"}))
    ];

    for (const e of allEdges) {
        const k = edgeKey(e.von_id, e.zu_id, e.kind);
        const st = EDGE_STATE.get(k);
        if (!st || st.flow <= 0) continue;

        if (e.kind === "dyn" && !(ALT_MODE && st.flow > 0)) continue;

        const a = node(e.von_id), b = node(e.zu_id);
        if (!a || !b) continue;

        const p1 = nodeToCanvas(a);
        const p2 = nodeToCanvas(b);
        const len = Math.hypot(p2.x - p1.x, p2.y - p1.y) || 1;

        const density = 0.18 * Math.max(0.35, Math.min(2.5, FLOW_SCALE));
        const count = Math.max(6, Math.min(300, Math.round(st.flow * density)));

        for (let i=0; i<count; i++) {
            particles.push({
                u: e.von_id,
                v: e.zu_id,
                kind: e.kind,
                t: Math.random(),
                speed: (45 + st.flow * 0.35) / len
            });
        }
    }
}

// ---------------- Hover / Click ----------------
let hover = { edge:null, node:null };

function getVisibleEdgesForPick() {
    const list = [];

    for (const e of EDGES_ORIG) {
        if (e.role === "alt_pre" && !ALT_MODE) continue;
        list.push({ e, kind:"orig" });
    }
    for (const e of EDGES_DYN) {
        const st = EDGE_STATE.get(edgeKey(e.von_id, e.zu_id, "dyn"));
        if (ALT_MODE && st && st.flow > 0) list.push({ e, kind:"dyn" });
    }
    return list;
}

// Forward Pan/Zoom (because map has pointer-events none)
let leafletPanning = false;
let lastMouse = { x:0, y:0 };

canvas.addEventListener("mousedown", (e) => {
    // Only pan if NOT hovering something
    if (hover.edge || hover.node) return;
    leafletPanning = true;
    userInteracted = true;
    lastMouse = { x: e.clientX, y: e.clientY };
});

window.addEventListener("mouseup", () => {
    leafletPanning = false;
});

window.addEventListener("mousemove", (e) => {
    if (!leafletPanning) return;
    const dx = lastMouse.x - e.clientX;
    const dy = lastMouse.y - e.clientY;
    lastMouse = { x: e.clientX, y: e.clientY };
    map.panBy([dx, dy], { animate: false });
});
// Canvas liegt über der Map -> deshalb Wheel/Pinch an Leaflet weiterreichen
canvas.addEventListener("wheel", (e) => {
    if (!overMapArea) return;

    // stoppt Seiten-Scroll/Zoom im Map-Bereich
    e.preventDefault();

    // Leaflet Zoom-Handler direkt nutzen
    if (map.scrollWheelZoom && map.scrollWheelZoom._onWheelScroll) {
        map.scrollWheelZoom._onWheelScroll(e);
    }
}, { passive: false });




canvas.addEventListener("mousemove", (evt) => {
    const rect = canvas.getBoundingClientRect();
    const mx = evt.clientX - rect.left;
    const my = evt.clientY - rect.top;

    hover.edge = null;
    hover.node = null;

    for (const n of NODES) {
        const p = nodeToCanvas(n);
        if (Math.hypot(mx - p.x, my - p.y) < 10) { hover.node = n; break; }
    }

    const pickEdges = getVisibleEdgesForPick();
    let best = {d: 9999, item:null};

    for (const it of pickEdges) {
        const a = node(it.e.von_id), b = node(it.e.zu_id);
        if (!a || !b) continue;
        const p1 = nodeToCanvas(a), p2 = nodeToCanvas(b);
        const d = distancePointToSegment(mx, my, p1.x, p1.y, p2.x, p2.y);
        if (d < 7 && d < best.d) best = { d, item: it };
    }
    if (best.item) hover.edge = best.item;

    if (hover.node) {
        const n = hover.node;
        tooltip.innerHTML = `
      <strong>${n.name || "Knoten"} (#${n.id})</strong><br>
      Typ: ${n.typ || "-"}<br>
      Land: ${n.land || "-"}<br>
      Güter Out: ${Number(n.gueter_out||0).toFixed(1)}<br>
      Güter In: ${Number(n.gueter_in||0).toFixed(1)}
    `;
        tooltip.style.left = (mx + 16) + "px";
        tooltip.style.top  = (my + 16) + "px";
        tooltip.classList.remove("hidden");
        return;
    }

    if (hover.edge) {
        const { e, kind } = hover.edge;
        const st = EDGE_STATE.get(edgeKey(e.von_id, e.zu_id, kind));
        const a = node(e.von_id), b = node(e.zu_id);

        const label =
            (kind === "dyn") ? "Alternative (dynamisch)" :
                (ALT_USED_ORIG.has(edgeKey(e.von_id, e.zu_id, "orig")) ? "Alternative (reroute)" :
                    (e.role === "alt_pre") ? "Alternative (vordefiniert)" :
                        "Original (Hauptroute)");

        tooltip.innerHTML = `
      <strong>${a?.name || e.von_id} → ${b?.name || e.zu_id}</strong><br>
      Typ: ${label}<br>
      Distanz: ${(e.distanz_km||0).toFixed(0)} km<br>
      Flow: ${(st?.flow||0).toFixed(1)}<br>
      Kapazität: ${kind === "orig" ? logicalCapForKey(edgeKey(e.von_id, e.zu_id, "orig")).toFixed(1) : "—"}<br>
      Überlastet: ${st?.overloaded ? "Ja" : "Nein"}<br>
      Blockiert: ${st?.blocked ? "Ja" : "Nein"}
    `;
        tooltip.style.left = (mx + 16) + "px";
        tooltip.style.top  = (my + 16) + "px";
        tooltip.classList.remove("hidden");
        return;
    }

    tooltip.classList.add("hidden");
});

canvas.addEventListener("click", () => {
    if (!hover.edge) return;
    const { e, kind } = hover.edge;

    // ONLY block/unblock main orig edges
    if (kind !== "orig") return;
    if (e.role !== "main") return;

    const k = edgeKey(e.von_id, e.zu_id, "orig");
    const st = EDGE_STATE.get(k);
    if (!st) return;

    st.blocked = !st.blocked;
    recalc();
});

// ---------------- Stats ----------------
function updateStats() {
    let flowSum = 0;
    let blocked = 0;
    let overloadedMain = 0;
    let visibleEdges = 0;
    let altVol = 0;

    for (const e of EDGES_ORIG) {
        const st = EDGE_STATE.get(edgeKey(e.von_id, e.zu_id, "orig"));
        if (!st) continue;

        flowSum += st.flow;
        if (st.blocked) blocked++;
        if (st.overloaded && e.role === "main") overloadedMain++;

        if (e.role === "main") visibleEdges++;
        else if (ALT_MODE && e.role === "alt_pre") visibleEdges++;

        if (ALT_USED_ORIG.has(edgeKey(e.von_id, e.zu_id, "orig"))) altVol += st.flow;
        if (ALT_MODE && e.role === "alt_pre") altVol += st.flow;
    }

    for (const e of EDGES_DYN) {
        const st = EDGE_STATE.get(edgeKey(e.von_id, e.zu_id, "dyn"));
        if (!st) continue;

        flowSum += st.flow;
        if (ALT_MODE && st.flow > 0) {
            visibleEdges++;
            altVol += st.flow;
        }
    }

    const altUsed = altVol > 0.0001;

    statsEl.innerHTML = `
    <div><strong>Gesamtvolumen:</strong> ~${Math.round(flowSum)} Einheiten / Zyklus</div>
    <div><strong>Aktive Kanten:</strong> ${visibleEdges} (gesperrt: ${blocked})</div>
    <div><strong>Partikel:</strong> ${particles.length} · Überlastet: ${overloadedMain}</div>
    <div><strong>Alternativ genutzt:</strong> ${altUsed ? "Ja" : "Nein"} (Volumen: ${Math.round(altVol)})</div>
    <div style="opacity:.85"><strong>Flow-Skala:</strong> ${Math.round(FLOW_SCALE*100)}%</div>
  `;
}

// ---------------- Drawing ----------------
function draw(delta) {
    ctx.clearRect(0, 0, width, height);

    const allEdges = [
        ...EDGES_ORIG.map(e => ({ ...e, kind: "orig" })),
        ...EDGES_DYN.map(e => ({ ...e, kind: "dyn" }))
    ];

    for (const e of allEdges) {
        const kind = e.kind;
        const k = edgeKey(e.von_id, e.zu_id, kind);
        const st = EDGE_STATE.get(k);
        if (!st) continue;

        const a = node(e.von_id), b = node(e.zu_id);
        if (!a || !b) continue;

        const p1 = nodeToCanvas(a), p2 = nodeToCanvas(b);

        const isDyn = (kind === "dyn");
        const isMainOrig = (!isDyn && e.role === "main");
        const isRerouteOrig = (!isDyn && ALT_MODE && ALT_USED_ORIG.has(edgeKey(e.von_id, e.zu_id, "orig")));
        const isAltPre = (!isDyn && e.role === "alt_pre");

        if (isAltPre && !ALT_MODE) continue;
        if (isDyn && !(ALT_MODE && st.flow > 0)) continue;

        if (isMainOrig && st.blocked) {
            ctx.setLineDash([6,4]);
            ctx.lineWidth = 1.8;
            ctx.strokeStyle = "rgba(148,163,184,0.55)";
        } else {
            ctx.setLineDash([]);

            if (isMainOrig && st.overloaded) {
                const pulse = 1 + 0.25 * Math.sin(timeMs / 220);
                ctx.lineWidth = 3.8 * pulse;
                ctx.strokeStyle = "rgba(248,113,113,0.95)";
            } else if (isDyn || isAltPre || isRerouteOrig) {
                ctx.lineWidth = (st.flow > 0) ? 2.8 : 1.8;
                ctx.strokeStyle = "rgba(245,158,11,0.90)";
            } else {
                const hasFlow = st.flow > 0;
                ctx.lineWidth = hasFlow ? 2.3 : 1.1;
                ctx.strokeStyle = hasFlow ? "rgba(59,130,246,0.88)" : "rgba(59,130,246,0.25)";
            }
        }

        ctx.beginPath();
        ctx.moveTo(p1.x, p1.y);
        ctx.lineTo(p2.x, p2.y);
        ctx.stroke();
    }

    // particles
    if (running) {
        const dt = delta / 1000;

        for (const p of particles) {
            const a = node(p.u), b = node(p.v);
            if (!a || !b) continue;

            const p1 = nodeToCanvas(a), p2 = nodeToCanvas(b);

            p.t += p.speed * dt;
            if (p.t > 1) p.t -= 1;

            const x = p1.x + (p2.x - p1.x) * p.t;
            const y = p1.y + (p2.y - p1.y) * p.t;

            const kOrig = edgeKey(p.u, p.v, "orig");
            const isGold = (p.kind === "dyn") || (ALT_MODE && ALT_USED_ORIG.has(kOrig));

            ctx.beginPath();
            ctx.fillStyle = isGold ? "rgba(245,158,11,0.95)" : "rgba(34,197,94,0.95)";
            ctx.arc(x, y, 2.6, 0, Math.PI * 2);
            ctx.fill();
        }
    }

    // nodes + labels
    for (const n of NODES) {
        const p = nodeToCanvas(n);

        ctx.beginPath();
        ctx.fillStyle = "rgba(15,23,42,0.95)";
        ctx.arc(p.x, p.y, 7.0, 0, Math.PI * 2);
        ctx.fill();

        ctx.beginPath();
        ctx.strokeStyle = "rgba(148,163,184,0.85)";
        ctx.lineWidth = 1.2;
        ctx.arc(p.x, p.y, 7.0, 0, Math.PI * 2);
        ctx.stroke();

        const label = (n.name && String(n.name).trim()) ? String(n.name) : String(n.id);
        ctx.font = "11px system-ui";
        ctx.fillStyle = "#e5e7eb";
        ctx.textAlign = "center";
        ctx.textBaseline = "bottom";
        ctx.fillText(label, p.x, p.y - 9);
    }
}

// ---------------- Loop ----------------
let last = performance.now();
function loop(now) {
    const delta = now - last;
    last = now;
    timeMs += delta;

    draw(delta);
    requestAnimationFrame(loop);
}

// ---------------- Buttons ----------------
btnToggle.addEventListener("click", () => {
    running = !running;
    btnToggle.textContent = running ? "⏸ Pause" : "▶ Start";
});

btnReset.addEventListener("click", () => {
    for (const st of EDGE_STATE.values()) {
        st.blocked = false;
        st.flow = 0;
        st.overloaded = false;
    }
    EDGES_DYN = [];
    particles = [];
    ALT_MODE = false;
    ALT_USED_ORIG = new Set();
    userInteracted = false;

    fitMapToNodes();
    recalc();
});

// ---------------- Slider ----------------
function setFlowScaleFromSlider() {
    if (!flowSlider) return;
    const val = Number(flowSlider.value || 100);
    FLOW_SCALE = Math.max(0.3, Math.min(2.5, val / 100));
    if (flowValue) flowValue.textContent = `${Math.round(FLOW_SCALE*100)}%`;
}

if (flowSlider) {
    setFlowScaleFromSlider();
    flowSlider.addEventListener("input", () => {
        setFlowScaleFromSlider();
        recalc();
    });
}

// ---------------- Init ----------------
(async function init(){
    // IMPORTANT: force leaflet to compute sizes first
    setTimeout(() => {
        map.invalidateSize();
        resizeCanvasToMap();
    }, 0);

    await loadNetwork();
    setFlowScaleFromSlider();
    recalc();
    updateStats();
    requestAnimationFrame(loop);
})();
