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

for (const t of traces) {
  const d = el(
    "details",
    "hide-internal" + (t.o ? " nixpkgs-origin-entry" : ""),
  );
  d.dataset.nixpkgsSource = t.n;
  d.dataset.nixpkgsOrigin = t.o;
  d.dataset.src = t.s;
  const sm = el("summary"),
    sr = el("span", "summary-row");
  sr.append(el("span", "summary-path", t.s));
  if (t.o) sr.append(el("span", "origin-tag", "nixpkgs"));
  sm.append(sr);
  d.append(sm);
  d.ontoggle = () => {
    if (d.open) renderEntry(d, t);
  };
  E.append(d);
}

const originToggle = document.getElementById("show-nixpkgs-origin");
const showOrigin = () =>
  E.classList.toggle("hide-nixpkgs-origin", !originToggle.checked);
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
