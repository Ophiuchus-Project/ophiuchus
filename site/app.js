// Ophiuchus public page. Plain JS, no third-party requests. All record text is escaped before display.
"use strict";
const D = "data/";
const TYPES = {snf: "Skilled nursing facility", hha: "Home health agency", fqhc: "Federally qualified health center",
  hospital: "Hospital", hospice: "Hospice", rhc: "Rural health clinic"};
const PLURAL = {hha: "home health agencies", fqhc: "federally qualified health centers", hospital: "hospitals", hospice: "hospices", rhc: "rural health clinics"};
const CARE_COMPARE = {snf: "nursing-home", hospital: "hospital", hha: "home-health", hospice: "hospice"};
const OWNERSHIP = {P: "For-profit (proprietary)", N: "Nonprofit", D: "CMS ownership code D (not defined in the CMS data dictionary)"};
const STATES = {AL: "Alabama", AK: "Alaska", AZ: "Arizona", AR: "Arkansas", CA: "California", CO: "Colorado", CT: "Connecticut",
  DE: "Delaware", DC: "District of Columbia", FL: "Florida", GA: "Georgia", HI: "Hawaii", ID: "Idaho", IL: "Illinois", IN: "Indiana",
  IA: "Iowa", KS: "Kansas", KY: "Kentucky", LA: "Louisiana", ME: "Maine", MD: "Maryland", MA: "Massachusetts", MI: "Michigan",
  MN: "Minnesota", MS: "Mississippi", MO: "Missouri", MT: "Montana", NE: "Nebraska", NV: "Nevada", NH: "New Hampshire",
  NJ: "New Jersey", NM: "New Mexico", NY: "New York", NC: "North Carolina", ND: "North Dakota", OH: "Ohio", OK: "Oklahoma",
  OR: "Oregon", PA: "Pennsylvania", RI: "Rhode Island", SC: "South Carolina", SD: "South Dakota", TN: "Tennessee", TX: "Texas",
  UT: "Utah", VT: "Vermont", VA: "Virginia", WA: "Washington", WV: "West Virginia", WI: "Wisconsin", WY: "Wyoming",
  PR: "Puerto Rico", GU: "Guam", VI: "U.S. Virgin Islands", AS: "American Samoa", MP: "Northern Mariana Islands", XX: "No state in the CMS record"};
const STAGE_ORDER = ["excluded", "fined", "payment denied", "cited: harm-level deficiency"];
const STOP = new Set(["llc", "inc", "the", "and", "of", "corp", "co", "lp", "ltd", "pllc", "pc", "dba", "for", "at"]);
const PAGE = 500;
const SEVERITY = "scope and severity G or above; J, K and L are immediate jeopardy";
let IX = null, REPLIES = [];
const cache = {};

function esc(s) {
  return String(s == null ? "" : s).replace(/[&<>"']/g, c => ({"&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"}[c]));
}
function get(path) {
  if (!(path in cache)) {
    cache[path] = fetch(D + path).then(r => { if (!r.ok) throw new Error(path + ": " + r.status); return r.json(); });
    cache[path].catch(() => delete cache[path]);
  }
  return cache[path];
}
function words(s) { return (String(s || "").toLowerCase().match(/[a-z0-9]+/g) || []); }
function usd(n) { return "$" + Number(n).toLocaleString("en-US", {maximumFractionDigits: 0}); }
function kb(n) { return n > 1048576 ? (n / 1048576).toFixed(1) + " MB" : Math.round(n / 1024) + " KB"; }
function stateName(s) { return STATES[s] || s; }
function plural(n, one, many) { return `${Number(n).toLocaleString()} ${n === 1 ? one : (many || one + "s")}`; }
function day(d) { return d ? esc(d) : "no date in the record"; }
function started(d) {
  if (!d) return "";
  if (d < "1900-01-01") return `no usable start date in the record (${esc(d)})`;
  if (d > IX.built) return `listed to start ${esc(d)} (a future date in the record)`;
  return `since ${esc(d)}`;
}
function sectionOf(a) {     // HHS-OIG exclusion types, as the LEIE lists them
  const s = String(a || "").trim();
  let m = /^1128([ab])(\d+)$/i.exec(s);
  if (m) return `under section 1128(${m[1].toLowerCase()})(${m[2]}) of the Social Security Act`;
  m = /^1128A(a)?$/i.exec(s); if (m) return "under section 1128A of the Social Security Act";
  if (/^1156$/.test(s)) return "under section 1156 of the Social Security Act";
  if (/^BRCH\s*CIA$/i.test(s)) return "for breach of a Corporate Integrity Agreement";
  if (/^BRCH\s*SA$/i.test(s)) return "for breach of a Settlement Agreement";
  return `(exclusion type "${esc(s || "not stated")}" as HHS-OIG lists it)`;
}
function shard(id) { return sha1hex(id).slice(0, 2); }

// SHA-1 (only to find the owner file; must match page.py owner_shard)
function sha1hex(str) {
  const b = new TextEncoder().encode(str), l = b.length, n = ((l + 8 >> 6) + 1) * 16, w = new Array(n).fill(0);
  for (let i = 0; i < l; i++) w[i >> 2] |= b[i] << (24 - (i % 4) * 8);
  w[l >> 2] |= 0x80 << (24 - (l % 4) * 8); w[n - 1] = l * 8;
  let h0 = 0x67452301, h1 = 0xEFCDAB89, h2 = 0x98BADCFE, h3 = 0x10325476, h4 = 0xC3D2E1F0;
  const W = new Array(80), rol = (x, c) => (x << c) | (x >>> (32 - c));
  for (let i = 0; i < n; i += 16) {
    let a = h0, b2 = h1, c = h2, d = h3, e = h4;
    for (let t = 0; t < 80; t++) {
      W[t] = t < 16 ? w[i + t] : rol(W[t - 3] ^ W[t - 8] ^ W[t - 14] ^ W[t - 16], 1);
      const f = t < 20 ? (b2 & c) | (~b2 & d) : t < 40 ? b2 ^ c ^ d : t < 60 ? (b2 & c) | (b2 & d) | (c & d) : b2 ^ c ^ d;
      const k = t < 20 ? 0x5A827999 : t < 40 ? 0x6ED9EBA1 : t < 60 ? 0x8F1BBCDC : 0xCA62C1D6;
      const tmp = (rol(a, 5) + f + e + k + W[t]) | 0; e = d; d = c; c = rol(b2, 30); b2 = a; a = tmp;
    }
    h0 = (h0 + a) | 0; h1 = (h1 + b2) | 0; h2 = (h2 + c) | 0; h3 = (h3 + d) | 0; h4 = (h4 + e) | 0;
  }
  return [h0, h1, h2, h3, h4].map(x => (x >>> 0).toString(16).padStart(8, "0")).join("");
}

// ---- citations, corrections, replies --------------------------------------------------------------------------------
function mailto(kind, id) {
  return `mailto:${esc(IX.contact)}?subject=${encodeURIComponent(`Ophiuchus ${kind} ${id}`)}`;
}
function act(id, canReply) {
  return `<details class="act"><summary>Correct or reply</summary><p>Item <code>${esc(id)}</code>.
    <a href="${mailto("correction", id)}">Report a correction</a>${canReply ? ` · <a href="${mailto("reply", id)}">Send a reply (up to 150 words)</a>` : ""}.
    No mail program? Write to ${esc(IX.contact)} with the item code in the subject.</p></details>`;
}
function srcText(i, inline, asOf) {
  const s = IX.sources[i] || {};
  const link = s.page || s.file;
  const name = link ? `<a href="${esc(link)}" rel="noopener">${esc(s.label)}</a>` : esc(s.label);
  const file = s.file && s.page ? ` (<a href="${esc(s.file)}" rel="noopener">file</a>)` : "";
  return `<span class="src">${inline ? "Source: " : ""}${name}${file}${s.data_date ? `, CMS data of ${esc(s.data_date)}` : ""}, as of ${esc(asOf || s.read)} (date read)</span>`;
}
function notesFor(id) {
  const c = (IX.corrections || []).filter(x => x.item === id)
    .map(x => `<p class="note">Corrected ${esc(x.date)}: ${esc(x.note)}</p>`).join("");
  const r = REPLIES.filter(x => x.item === id)
    .map(x => `<div class="reply"><p class="reply-by">Reply from ${esc(x.attribution)}, ${esc(x.date)}:</p><blockquote data-quote-src="reply ${esc(x.date)}">${esc(x.text)}</blockquote></div>`).join("");
  return c + r;
}
function namedHere(id, who) {
  return `<aside class="named"><p><strong>Named here?</strong> ${who} can ask us to correct a role, share or date, or send a reply of up to 150 words, which is shown under the entry.</p>
    <p><a class="btn" href="${mailto("correction", id)}">Send a correction</a> <a class="btn" href="${mailto("reply", id)}">Send a reply</a> <span class="hint">or write to ${esc(IX.contact)}</span></p></aside>`;
}

// ---- policy section 4: the only wording an enforcement record can take ---------------------------------------------
function enforcementText(e) {
  const asof = "";     // the data date and the "as of" date are on the item's source line
  if (e.kind === "leie_exclusion" && e.stage === "excluded") {
    const w = e.waiver_date ? ` HHS-OIG lists a waiver from ${esc(e.waiver_date)}${e.waiver_state ? ` (${esc(e.waiver_state)})` : ""}.` : "";
    return `<strong>excluded</strong> by HHS-OIG ${sectionOf(e.authority)}, from ${day(e.active_from)}` +
      `${e.active_to ? ` to ${esc(e.active_to)}` : ", no end date in the record"}. HHS-OIG lists this NPI as ` +
      `<q data-quote-src="HHS-OIG LEIE">${esc(e.leie_name)}</q>, ${esc(e.leie_state)}.${w} Exclusions can be limited in scope, waived or later lifted. ${asof}`;
  }
  if (e.kind === "nursing_home_enforcement") {
    const win = `${day(e.active_from)} to ${day(e.active_to)}`;
    if (e.stage === "fined")
      return `<strong>fined</strong> by CMS: ${plural(e.count, "fine")}, ${usd(e.amount)} in total (sum of the fine amounts CMS lists), penalty dates ${win}. ${asof}`;
    if (e.stage === "payment denied")
      return `<strong>payment denied</strong> by CMS: ${plural(e.count, "denial")} of payment, start dates ${win}. ${asof}`;
    if (e.stage === "cited: harm-level deficiency") {
      const sev = Object.entries(e.severities || {}).map(([k, v]) => `${esc(k)}: ${v}`).join(", ");
      const disp = e.disputed ? ` ${plural(e.disputed, "of these is", "of these are")} under informal dispute resolution, as CMS marks them.` : "";
      return `<strong>cited: harm-level deficiency</strong> by CMS: ${plural(e.count, "citation")} at ${SEVERITY} (${sev}), survey dates ${win}.${disp} ${asof}`;
    }
  }
  return null;    // unknown kind or stage: not shown (the publish checks fail before this can reach the page)
}

function coverage(ft) {
  return ft === "snf"
    ? "Checked: HHS-OIG exclusions (by NPI) and CMS nursing-home penalties and health citations (about the last three years)."
    : `Checked: HHS-OIG exclusions (by NPI) only. CMS nursing-home penalty and citation files do not cover ${esc(PLURAL[ft] || "this type of facility")}.`;
}

function enforcementSection(f) {
  const rows = (f.e || []).slice().sort((a, b) => STAGE_ORDER.indexOf(a.stage) - STAGE_ORDER.indexOf(b.stage))
    .map(e => { const t = enforcementText(e); return t ? `<li id="${esc(e.id)}">${t} ${srcText(e.s, true, e.as_of)}${act(e.id, true)}${notesFor(e.id)}</li>` : ""; }).join("");
  const groups = (f.g || []).map(g => `<li class="plain">CMS lists ${plural(g.count, "citation")} (all severity levels) in its category <q data-quote-src="CMS health citations, Deficiency Category">${esc(g.category)}</q>, survey dates ${day(g.from)} to ${day(g.to)}. ${srcText(g.s, true, g.as_of)}</li>`).join("");
  return `<p class="hint">${coverage(f.ft)}</p>` + (rows || groups ? `<ul class="enf">${rows}${groups}</ul>` : `<p class="none">None found in the files read.</p>`);
}

function ownersSection(f) {
  const byGroup = {};
  for (const l of f.o) { const g = IX.role_group[l[3]]; (byGroup[g] = byGroup[g] || []).push(l); }
  const srcs = [...new Set(f.o.map(l => l[8]))];
  const groups = Object.keys(byGroup).map(Number).sort((a, b) => a - b).map(g => {
    const rows = byGroup[g].sort((a, b) => (parseFloat(b[5]) || 0) - (parseFloat(a[5]) || 0) || String(a[1]).localeCompare(String(b[1])))
      .map(([oid, nm, kind, role, title, pct, date, flags]) => {
        const id = `${f.id}|${oid}|${IX.role_codes[role]}`;
        const share = IX.role_share[role] && pct && parseFloat(pct) > 0 ? `${esc(pct)}%` : "";
        const bits = [title ? esc(title.toLowerCase()) : "", share, started(date)].filter(Boolean).join("; ");
        const fl = (flags || []).length ? ` <span class="flagnote">filing describes this owner as: ${flags.map(x => `<span class="flag">${esc(x.toLowerCase())}</span>`).join(" ")}</span>` : "";
        return `<li id="${esc(id)}"><a href="#o/${esc(oid)}">${nm ? esc(nm) : `<span class="withheld">(no name in the CMS record; PAC ID ${esc(oid.replace("pac:", ""))})</span>`}</a>
          <span class="role">${esc(IX.role_plain[role])}${kind === "p" ? ", individual" : ""}</span>${bits ? ` · ${bits}` : ""}${fl}${act(id, true)}${notesFor(id)}</li>`;
      }).join("");
    return `<h4>${esc(IX.groups[g])}</h4><ul class="owners">${rows}</ul>`;
  }).join("");
  const wh = Object.entries(f.w || {}).map(([r, n]) => `${plural(n, "personal trust or estate", "personal trusts or estates")} listed as ${esc(IX.role_plain[r])}`).join("; ");
  const ct = Object.entries(f.x || {}).map(([r, n]) => `${n} listed as ${esc(IX.role_plain[r])}`).join("; ");
  return `<p class="hint">Source: ${srcs.map(s => srcText(s, false)).join("; ") || "CMS All Owners files"}. Shares as each filing reports them; no totals.${f.en > 1 ? ` This facility has ${f.en} CMS enrollments; an owner listed the same way in more than one is shown once.` : ""}</p>
    ${groups || `<p class="none">No named owners in the CMS file.</p>`}
    ${wh ? `<p class="counted">Names withheld: ${wh}.</p>` : ""}
    ${ct ? `<p class="counted">Individuals CMS lists who are counted, not named: ${ct}.</p>` : ""}`;
}

function facilityCard(f, st) {
  const name = f.nm[f.nm.length - 1] || f.id;
  const cc = CARE_COMPARE[f.ft] && f.id.startsWith("ccn:") ? ` · <a href="https://www.medicare.gov/care-compare/details/${CARE_COMPARE[f.ft]}/${esc(f.id.slice(4))}" rel="noopener">Medicare Care Compare page</a>` : "";
  return `<article class="card">
    <h2 tabindex="-1">${esc(name)}</h2>
    ${f.nm.length > 1 ? `<p class="aka">Also recorded as: ${f.nm.slice(0, -1).map(esc).join("; ")}</p>` : ""}
    <dl class="facts">
      <dt>Type</dt><dd>${esc(TYPES[f.ft] || f.ft)}</dd>
      <dt>Ownership</dt><dd>${esc(OWNERSHIP[f.pn] || "not stated")}</dd>
      <dt>Location</dt><dd>${esc(f.ad)}${f.adr ? ` <span class="hint">(street not shown: an individual holds an ownership role in this facility, which may be run from a home)</span>` : ""}</dd>
      <dt>CMS certification number</dt><dd>${esc(f.id.replace(/^(ccn|pecos_enr):/, ""))}${cc}</dd>
    </dl>
    <h3>Enforcement records</h3>${enforcementSection(f)}
    <h3>Owners and officers, as CMS lists them</h3>${ownersSection(f)}
    ${namedHere(f.id, "An organisation or a person named on this page")}
    <p class="links"><a href="#st/${esc(st)}">All facilities in ${esc(stateName(st))}</a> · <button type="button" class="copy" data-href="${esc(location.href)}">Copy link to this record</button></p>
    <p class="hint printonly">Ophiuchus ${esc(IX.version)} · ${esc(location.href)}</p>
  </article>`;
}

// ---- views ---------------------------------------------------------------------------------------------------------
function setView(html, title) {
  const v = document.getElementById("view");
  v.innerHTML = html;
  document.title = title ? `${title} — Ophiuchus` : "Ophiuchus: who owns US healthcare facilities";
  const h = v.querySelector("h2");
  if (h) { h.setAttribute("tabindex", "-1"); h.focus({preventScroll: true}); v.scrollIntoView(); }
}
function loading(what, bytes) {
  document.getElementById("view").innerHTML = `<p class="loading" role="status">Loading ${esc(what)}${bytes ? ` (${kb(bytes)})` : ""}…</p>`;
}

async function showFacility(st, id) {
  loading(`${stateName(st)} facilities`, IX.state_bytes[st]);
  const list = await get(`fac/${encodeURIComponent(st)}.json`);
  const f = list.find(x => x.id === id);
  if (!f) return setView(`<p>Facility ${esc(id)} is not in this data version.</p>`, "Not found");
  setView(facilityCard(f, st), f.nm[f.nm.length - 1]);
  if (location.hash.includes("~")) { const t = document.getElementById(decodeURIComponent(location.hash.split("~")[1])); if (t) t.scrollIntoView(); }
}

async function showOwner(id) {
  loading("owner");
  const d = await get(`owners/${shard(id)}.json`);
  const o = d[id];
  if (!o) return setView(`<p>${esc(id)} is not in this data version.</p>`, "Not found");
  const facs = new Map();
  for (const x of o.f) { if (!facs.has(x[0])) facs.set(x[0], []); facs.get(x[0]).push(x); }
  const states = {};
  for (const [ccn, xs] of facs) (states[xs[0][2]] = states[xs[0][2]] || []).push([ccn, xs]);
  const withRec = [...facs.values()].filter(xs => xs[0][7]).length;
  const body = Object.keys(states).sort().map(st => {
    const items = states[st].map(([ccn, xs]) => {
      const roles = xs.map(([, , , role, pct, date]) => `${esc(IX.role_plain[role])}${IX.role_share[role] && pct && parseFloat(pct) > 0 ? ` ${esc(pct)}%` : ""}${date ? `, ${started(date)}` : ""}`).join("; ");
      const first = xs.map(x => x[5]).filter(Boolean).sort()[0];
      const recEnd = xs[0][8];
      const rec = xs[0][7] ? ` · <span class="hasrec">the facility has HHS-OIG or CMS nursing-home records${first && recEnd && recEnd < first ? " (all dated before this owner's listed start)" : ""}</span>` : "";
      return `<li><a href="#f/${esc(st)}/${esc(ccn)}">${esc(xs[0][1])}</a>: ${roles}${rec}</li>`;
    }).join("");
    return `<details ${Object.keys(states).length <= 3 ? "open" : ""}><summary>${esc(stateName(st))}: ${plural(states[st].length, "facility", "facilities")}</summary><ul>${items}</ul></details>`;
  }).join("");
  setView(`<article class="card">
    <h2>${o.nm ? esc(o.nm) : `<span class="withheld">(no name in the CMS record)</span>`}</h2>
    <dl class="facts">
      <dt>Listed as</dt><dd>${o.k === "p" ? "An individual, named only in the roles CMS lists below" : "An organisation"}</dd>
      <dt>CMS PAC ID</dt><dd>${esc(id.replace("pac:", ""))}</dd>
      ${o.fl.length ? `<dt>Enrollment filings describe it as</dt><dd>${o.fl.map(x => `<span class="flag">${esc(x.toLowerCase())}</span>`).join(" ")}</dd>` : ""}
      <dt>Roles</dt><dd>${plural(o.f.length, "role")} at ${plural(facs.size, "facility", "facilities")} in ${plural(Object.keys(states).length, "state")}</dd>
      <dt>Facility records</dt><dd>${withRec} of ${plural(facs.size, "facility", "facilities")} ${withRec === 1 ? "carries its" : "carry their"} own HHS-OIG or CMS nursing-home records (see each facility; the records belong to the facility, not to this owner)</dd>
    </dl>
    ${body}
    ${namedHere(id, o.k === "p" ? "If this is you, you" : "This organisation")}
    <p class="links"><button type="button" class="copy" data-href="${esc(location.href)}">Copy link to this record</button></p>
  </article>`, o.nm || id);
}

function showStates() {
  setView(`<article class="card"><h2>Facilities by state</h2><ul class="states">${Object.entries(IX.states)
    .map(([s, n]) => `<li><a href="#st/${esc(s)}">${esc(stateName(s))}</a> <span class="hint">${n.toLocaleString()}</span></li>`).join("")}</ul></article>`, "By state");
}

const FILTERS = [["all", "All"], ["enf", "With HHS-OIG or CMS records"], ["pe", "An owner described as private equity company"], ["reit", "An owner described as REIT"]];
async function showState(st, filter, pageNo) {
  loading(`${stateName(st)} facilities`, IX.state_bytes[st]);
  const list = await get(`fac/${encodeURIComponent(st)}.json`);
  const f = filter || "all", p = Math.max(1, parseInt(pageNo || "1", 10));
  const flag = name => x => x.o.some(l => (l[7] || []).includes(name));
  const keep = list.filter(x => f === "all" || (f === "enf" && x.e.length) || (f === "pe" && flag("PRIVATE EQUITY COMPANY")(x)) || (f === "reit" && flag("REIT")(x)) || x.ft === f);
  const opt = (arr) => arr.map(([k, t]) => `<a href="#st/${esc(st)}/${k}" ${k === f ? 'aria-current="true" class="on"' : ""}>${esc(t)}</a>`).join("");
  const pages = Math.max(1, Math.ceil(keep.length / PAGE));
  const rows = keep.slice((p - 1) * PAGE, p * PAGE).map(x => `<li data-n="${esc(words(x.nm.join(" ") + " " + (x.city || "")).join(" "))}"><a href="#f/${esc(st)}/${esc(x.id)}">${esc(x.nm[x.nm.length - 1] || x.id)}</a> · ${esc(TYPES[x.ft] || x.ft)} · ${esc(x.city || "")}${x.e.length ? ` · <span class="hasrec">has records</span>` : ""}</li>`).join("");
  const nav = pages > 1 ? `<p class="pager">Page ${p} of ${pages}: ${Array.from({length: pages}, (_, i) => i + 1).map(i => i === p ? `<strong>${i}</strong>` : `<a href="#st/${esc(st)}/${f}/${i}">${i}</a>`).join(" ")}</p>` : "";
  setView(`<article class="card"><h2>${esc(stateName(st))}: ${plural(keep.length, "facility", "facilities")}</h2>
    <fieldset class="filters"><legend>Records and owners</legend>${opt(FILTERS)}</fieldset>
    <fieldset class="filters"><legend>Type</legend>${opt(Object.entries(TYPES))}</fieldset>
    ${f === "enf" ? `<p class="hint">Nursing homes are checked against CMS penalties and citations and HHS-OIG exclusions; other types against HHS-OIG exclusions only.</p>` : ""}
    <label for="within">Filter this page by name or city</label> <input id="within" type="search" autocomplete="off">
    ${nav}<ul id="statelist">${rows}</ul>${nav}</article>`, stateName(st));
  document.getElementById("within").addEventListener("input", e => {
    const w = words(e.target.value);
    for (const li of document.querySelectorAll("#statelist li")) li.hidden = !w.every(t => li.dataset.n.split(" ").some(x => x.startsWith(t)));
  });
}

// ---- search ----------------------------------------------------------------------------------------------------------
let qTimer = null, firstHit = null;
async function search(q) {
  const out = document.getElementById("results"), count = document.getElementById("rcount");
  const all = words(q), ws = all.filter(w => w.length >= 3 && !STOP.has(w));
  firstHit = null;
  if (!q.trim()) { out.innerHTML = ""; count.textContent = ""; return; }
  if (!ws.length) { out.innerHTML = ""; count.textContent = "Type at least three letters of a distinctive word (not LLC, Inc, The)."; return; }
  let entries;
  try { entries = await get(`search/${ws[0].slice(0, 2)}.json`); } catch (e) { entries = []; }
  const scored = [];
  for (const e of entries) {
    const nw = words(e[0]);
    if (!ws.every(w => nw.some(x => x.startsWith(w)))) continue;
    const exact = nw.join(" ") === all.join(" ") ? 0 : nw[0] && nw[0].startsWith(ws[0]) ? 1 : 2;
    scored.push([exact, e[2] === "f" ? 0 : -(e[3] || 0), e]);
  }
  scored.sort((a, b) => a[0] - b[0] || a[1] - b[1] || String(a[2][0]).localeCompare(String(b[2][0])));
  const hits = scored.slice(0, 60).map(x => x[2]);
  count.textContent = scored.length ? `${scored.length > 60 ? `Showing 60 of ${scored.length.toLocaleString()}: add another word to narrow.` : `${plural(scored.length, "match", "matches")}.`}` :
    "No match. Try one distinctive word of the name, leave out LLC or Inc, or browse by state.";
  out.innerHTML = hits.length ? `<ul>${hits.map(e => {
    if (e[2] === "f") { const href = `#f/${e[3]}/${e[1]}`; firstHit = firstHit || href;
      return `<li><a href="${esc(href)}">${esc(e[0])}</a> <span class="kind">${esc(TYPES[e[5]] || "facility")}, ${esc(e[4])} ${esc(e[3])}${e[6] ? " · has records" : ""}</span></li>`; }
    const href = `#o/${e[1]}`; firstHit = firstHit || href;
    return `<li><a href="${esc(href)}">${e[0] ? esc(e[0]) : "(no name in the CMS record)"}</a> <span class="kind">${e[2] === "p" ? "individual (CMS-listed role)" : "organisation"} · ${plural(e[3], "facility", "facilities")}, mostly ${esc(e[4])} · PAC ID ${esc(e[1].replace("pac:", ""))}</span></li>`;
  }).join("")}</ul>` : "";
}

// ---- routing -----------------------------------------------------------------------------------------------------------
async function route() {
  const h = decodeURIComponent(location.hash.slice(1)).split("~")[0];
  const record = /^(f|o|st)\//.test(h) || h === "states";
  document.getElementById("about").hidden = record;
  document.getElementById("corrections").hidden = record;
  document.getElementById("search-box").hidden = record && h !== "states";
  try {
    if (h.startsWith("f/")) { const [, st, id] = h.split("/"); await showFacility(st, id); }
    else if (h.startsWith("o/")) await showOwner(h.slice(2));
    else if (h === "states") showStates();
    else if (h.startsWith("st/")) { const [, st, f, p] = h.split("/"); await showState(st, f, p); }
    else { document.getElementById("view").innerHTML = ""; document.title = "Ophiuchus: who owns US healthcare facilities";
      if (h === "about" || h === "corrections") document.getElementById(h).scrollIntoView(); }
  } catch (e) { setView(`<p class="error" role="alert">Could not load that part of the data (${esc(e.message)}). Try again, or reload the page.</p>`, "Error"); }
}

document.addEventListener("click", e => {
  const b = e.target.closest("button.copy");
  if (!b) return;
  const done = () => { b.textContent = "Link copied"; setTimeout(() => (b.textContent = "Copy link to this record"), 2000); };
  if (navigator.clipboard) navigator.clipboard.writeText(b.dataset.href).then(done, () => (b.textContent = b.dataset.href));
  else b.textContent = b.dataset.href;
});

(async function init() {
  try {
    IX = await get("index.json");
  } catch (e) {
    document.getElementById("meta").textContent = "The data could not be loaded. Reload the page to try again.";
    return;
  }
  try { const r = await fetch("replies.json"); if (r.ok) REPLIES = await r.json(); } catch (e) { REPLIES = []; }
  const dd = IX.data_dates || {};
  const short = Object.entries(dd).map(([k, v]) => `${esc(k)}: ${v.data ? `data of ${esc(v.data)}, ` : ""}read ${esc(v.read)}`);
  document.getElementById("meta").innerHTML = `Data version <strong>${esc(IX.version)}</strong> · ${IX.counts.facilities.toLocaleString()} facilities · refreshed weekly.`;
  document.getElementById("sources-list").innerHTML = short.map(s => `<li>${s}</li>`).join("");
  const c = document.getElementById("contact");
  c.href = "mailto:" + IX.contact; c.textContent = IX.contact;
  document.getElementById("unmatched").textContent = `${IX.counts.enforcement_facilities_not_in_enrollment} nursing homes with CMS penalty or citation records are not in the current CMS enrollment files (closed, merged or re-certified), so they have no facility entry here.`;
  const log = (IX.corrections || []).map(x => `<li>${esc(x.date)} · <code>${esc(x.item)}</code>: was "${esc(x.old)}", now "${esc(x.new)}". ${esc(x.note)}</li>`).join("");
  document.getElementById("changelog").innerHTML = `<h3>Change log</h3>${log ? `<ul>${log}</ul>` : "<p>No corrections yet.</p>"}`;
  const q = document.getElementById("q");
  q.addEventListener("input", () => { clearTimeout(qTimer); qTimer = setTimeout(() => search(q.value), 200); });
  document.getElementById("search-form").addEventListener("submit", e => { e.preventDefault(); if (firstHit) location.hash = firstHit; });
  window.addEventListener("hashchange", route);
  route();
})();
