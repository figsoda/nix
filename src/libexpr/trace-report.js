const E = document.getElementById("entries");

const el = (t, c, x) => {
  const e = document.createElement(t);
  if (c) e.className = c;
  if (x != null) e.textContent = x;
  return e;
};

const copyIcon = () => {
  const s = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  s.setAttribute("viewBox", "0 0 24 24");
  for (const d of ["M8 8h10v12H8z", "M6 16H4V4h12v2"]) {
    const p = document.createElementNS("http://www.w3.org/2000/svg", "path");
    p.setAttribute("d", d);
    s.append(p);
  }
  return s;
};

const copyBtn = (x) => {
  const b = el("button", "copy-button");
  b.type = "button";
  b.title = "copy";
  b.setAttribute("aria-label", "copy");
  b.append(copyIcon());
  b.onclick = async () => {
    try {
      await navigator.clipboard.writeText(x);
    } catch (e) {
      const t = document.createElement("textarea");
      t.value = x;
      document.body.appendChild(t);
      t.select();
      document.execCommand("copy");
      t.remove();
    }
    b.title = "copied";
    setTimeout(() => (b.title = "copy"), 900);
  };
  return b;
};

const pathRow = (x) => {
  const r = el("span", "path-row");
  r.append(el("span", "path-text", x), copyBtn(x));
  return r;
};

const renderEntry = (d, t) => {
  if (d.dataset.rendered) return;
  d.dataset.rendered = "true";

  const c = el("div", "fields");
  for (const [k, v] of t.e) c.append(el("b", null, k), pathRow(v));
  d.append(c);

  const tools = el("div", "entry-tools");
  const nl = el("label", "toggle"),
    ni = document.createElement("input");
  ni.className = "show-nixpkgs-lines";
  ni.type = "checkbox";
  ni.checked = true;
  nl.append(ni, "show nixpkgs frames");
  const il = el("label", "toggle"),
    ii = document.createElement("input");
  ii.className = "show-internal-lines";
  ii.type = "checkbox";
  il.append(ii, "show internal frames");
  tools.append(nl, il);
  d.append(tools);

  const fs = el("div", "frames");
  for (const id of t.f) {
    const f = frames[id];
    const r = el(
      "div",
      "frame" +
        (f.n ? " nixpkgs-frame" : "") +
        (f.i ? " internal-frame" : "") +
        (t.h ? "" : " missing"),
    );
    r.append(el("div", "message", f.m));
    if (f.p != null) {
      const p = el("div", "pos"),
        pr = el("span", "pos-row");
      pr.append(el("span", "path-text", f.p), copyBtn(f.p));
      p.append(pr);
      r.append(p);
    }
    if (f.c != null) r.append(el("pre", null, f.c));
    fs.append(r);
  }
  d.append(fs);

  const u = () => d.classList.toggle("hide-nixpkgs", !ni.checked);
  ni.onchange = u;
  u();
  const v = () => d.classList.toggle("hide-internal", !ii.checked);
  ii.onchange = v;
  v();
};

const buildEntry = (t, count, label) => {
  const d = el(
    "details",
    "hide-internal" + (t.o ? " nixpkgs-origin-entry" : ""),
  );
  const sm = el("summary"),
    sr = el("span", "summary-row");
  sr.append(el("span", "summary-path", label));
  if (count > 1) sr.append(el("span", "dup-count", "\u00d7" + count));
  if (t.o) sr.append(el("span", "origin-tag", "nixpkgs"));
  sm.append(sr);
  d.append(sm);
  d.ontoggle = () => {
    if (d.open) renderEntry(d, t);
  };
  return d;
};

const entryLabel = (t) => {
  let fallback = null;
  for (const id of t.f) {
    const f = frames[id];
    if (f.p == null) continue;
    if (!f.i) return f.p;
    if (fallback == null) fallback = f.p;
  }
  return fallback != null ? fallback : frames[t.f[0]].m;
};

const groups = new Map();
for (const t of traces) {
  const k = JSON.stringify([t.s, t.e]);
  let g = groups.get(k);
  if (!g) groups.set(k, (g = []));
  g.push(t);
}

const groupBadges = [];

for (const g of groups.values()) {
  const t = g[0];
  const dupCounts = new Map(),
    uniques = [];
  for (const x of g) {
    const k = JSON.stringify([x.h, x.f]);
    if (!dupCounts.has(k)) {
      dupCounts.set(k, 0);
      uniques.push([k, x]);
    }
    dupCounts.set(k, dupCounts.get(k) + 1);
  }

  let d;
  if (uniques.length === 1) {
    d = buildEntry(t, g.length, t.s);
  } else {
    d = el("details", "entry-group");
    if (g.every((x) => x.o)) d.classList.add("nixpkgs-origin-entry");
    const badge = el("span", "dup-count");
    groupBadges.push({
      badge,
      total: g.length,
      nonNixpkgs: g.filter((x) => !x.o).length,
    });
    const sm = el("summary"),
      sr = el("span", "summary-row");
    sr.append(el("span", "summary-path", t.s), badge);
    if (g.every((x) => x.o)) sr.append(el("span", "origin-tag", "nixpkgs"));
    sm.append(sr);
    d.append(sm);
    const inner = el("div", "group-entries");
    for (const [k, x] of uniques)
      inner.append(buildEntry(x, dupCounts.get(k), entryLabel(x)));
    d.append(inner);
  }
  d.dataset.nixpkgsSource = t.n;
  d.dataset.src = t.s;
  E.append(d);
}

const originToggle = document.getElementById("show-nixpkgs-origin");
const showOrigin = () => {
  const on = originToggle.checked;
  E.classList.toggle("hide-nixpkgs-origin", !on);
  for (const { badge, total, nonNixpkgs } of groupBadges)
    badge.textContent = "\u00d7" + (on ? total : nonNixpkgs);
};
originToggle.onchange = showOrigin;
showOrigin();
addEventListener("pageshow", showOrigin);

const searchField = document.getElementById("search");
const searchRegex = document.getElementById("search-regex");
const applyFilter = () => {
  const q = searchField.value;
  let match;
  if (!q) {
    match = null;
  } else if (searchRegex.checked) {
    try {
      const re = new RegExp(q, "i");
      match = (s) => re.test(s);
      searchField.classList.remove("regex-bad");
    } catch (e) {
      searchField.classList.add("regex-bad");
      match = null;
    }
  } else {
    searchField.classList.remove("regex-bad");
    const ql = q.toLowerCase();
    match = (s) => s.toLowerCase().includes(ql);
  }
  for (const d of E.children)
    d.classList.toggle("hide-filter", match && !match(d.dataset.src));
};
searchField.oninput = applyFilter;
searchRegex.onchange = applyFilter;
