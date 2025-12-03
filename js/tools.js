/* js/tools.js - fully working Compiler Toolkit logic */

/* ------- utilities ------- */
function toast(msg) {
  const el = document.createElement('div');
  el.textContent = msg;
  Object.assign(el.style, {
    position: 'fixed',
    right: '18px',
    bottom: '18px',
    background: '#111827',
    color: '#f9fafb',
    padding: '8px 12px',
    borderRadius: '8px',
    zIndex: 9999,
    fontSize: '13px'
  });
  document.body.appendChild(el);
  setTimeout(() => el.remove(), 1400);
}
function escapeHtml(s) {
  return (s + '')
    .replace(/&/g,'&amp;')
    .replace(/</g,'&lt;')
    .replace(/>/g,'&gt;');
}

/* ------- grammar utils ------- */
function parseGrammar(text) {
  const lines = text.split('\n').map(l => l.trim()).filter(Boolean);
  const prods = {};
  for (const line of lines) {
    const idx = line.indexOf('->');
    if (idx === -1) continue;
    const lhs = line.slice(0, idx).trim();
    const rhs = line.slice(idx + 2).trim();
    const alts = rhs.split('|').map(a => a.trim()).filter(Boolean);
    if (!prods[lhs]) prods[lhs] = [];
    for (const alt of alts) {
      const toks = alt === '' ? ['ε'] :
        alt.split(/\s+/).map(t => (t === 'epsilon' ? 'ε' : t));
      prods[lhs].push(toks.length ? toks : ['ε']);
    }
  }
  return prods;
}
function stringifyGrammar(prods) {
  return Object.keys(prods)
    .map(A => `${A} -> ${prods[A].map(r => r.join(' ')).join(' | ')}`)
    .join('\n');
}
function identifySymbols(prods) {
  const nonterm = new Set(Object.keys(prods));
  const terms = new Set();
  for (const [A, rhss] of Object.entries(prods)) {
    for (const rhs of rhss) {
      for (const t of rhs) {
        if (t !== 'ε' && !nonterm.has(t)) terms.add(t);
      }
    }
  }
  return {
    nonterminals: Array.from(nonterm),
    terminals: Array.from(terms),
    start: Object.keys(prods)[0] || null
  };
}

/* ------- FIRST / FOLLOW ------- */
function computeFirst(prods) {
  const FIRST = {};
  const nonterminals = new Set(Object.keys(prods));
  for (const A of nonterminals) FIRST[A] = new Set();

  let changed = true;
  while (changed) {
    changed = false;
    for (const [A, rhss] of Object.entries(prods)) {
      for (const rhs of rhss) {
        let nullablePrefix = true;
        for (const sym of rhs) {
          if (sym === 'ε') {
            if (!FIRST[A].has('ε')) { FIRST[A].add('ε'); changed = true; }
            nullablePrefix = false;
            break;
          }
          if (!nonterminals.has(sym)) {
            if (!FIRST[A].has(sym)) { FIRST[A].add(sym); changed = true; }
            nullablePrefix = false;
            break;
          }
          const set = FIRST[sym];
          for (const t of set) {
            if (t !== 'ε' && !FIRST[A].has(t)) { FIRST[A].add(t); changed = true; }
          }
          if (!set.has('ε')) { nullablePrefix = false; break; }
        }
        if (nullablePrefix) {
          if (!FIRST[A].has('ε')) { FIRST[A].add('ε'); changed = true; }
        }
      }
    }
  }
  return FIRST;
}

function firstOfString(rhs, FIRST, nonterminals) {
  const res = new Set();
  let nullable = true;
  for (const sym of rhs) {
    if (sym === 'ε') {
      res.add('ε');
      nullable = true;
      break;
    }
    if (!nonterminals.has(sym)) {
      res.add(sym);
      nullable = false;
      break;
    }
    const set = FIRST[sym];
    for (const t of set) if (t !== 'ε') res.add(t);
    if (!set.has('ε')) { nullable = false; break; }
  }
  if (nullable) res.add('ε');
  return res;
}

function computeFollow(prods, FIRST, startSymbol) {
  const FOLLOW = {};
  const nonterminals = new Set(Object.keys(prods));
  for (const A of nonterminals) FOLLOW[A] = new Set();
  if (startSymbol) FOLLOW[startSymbol].add('$');

  let changed = true;
  while (changed) {
    changed = false;
    for (const [A, rhss] of Object.entries(prods)) {
      for (const rhs of rhss) {
        for (let i = 0; i < rhs.length; i++) {
          const B = rhs[i];
          if (!nonterminals.has(B)) continue;

          const beta = rhs.slice(i + 1);
          if (beta.length > 0) {
            const fb = firstOfString(beta, FIRST, nonterminals);
            for (const t of fb) {
              if (t !== 'ε' && !FOLLOW[B].has(t)) {
                FOLLOW[B].add(t); changed = true;
              }
            }
            if (fb.has('ε')) {
              for (const t of FOLLOW[A]) {
                if (!FOLLOW[B].has(t)) { FOLLOW[B].add(t); changed = true; }
              }
            }
          } else {
            // B at end
            for (const t of FOLLOW[A]) {
              if (!FOLLOW[B].has(t)) { FOLLOW[B].add(t); changed = true; }
            }
          }
        }
      }
    }
  }
  return FOLLOW;
}

/* ------- LL(1) predictive table ------- */
function buildPredictiveTable(prods, FIRST, FOLLOW) {
  const table = {};
  const conflicts = [];
  const nonterminals = new Set(Object.keys(prods));

  for (const A of nonterminals) table[A] = {};

  for (const [A, rhss] of Object.entries(prods)) {
    for (const rhs of rhss) {
      const fs = firstOfString(rhs, FIRST, nonterminals);

      for (const t of fs) {
        if (t === 'ε') continue;
        table[A][t] = table[A][t] || [];
        table[A][t].push(rhs);
      }

      if (fs.has('ε')) {
        for (const b of FOLLOW[A] || []) {
          table[A][b] = table[A][b] || [];
          table[A][b].push(rhs);
        }
      }
    }
  }

  for (const [A, row] of Object.entries(table)) {
    for (const [t, list] of Object.entries(row)) {
      if (list.length > 1) {
        conflicts.push({
          nonterminal: A,
          terminal: t,
          prods: list
        });
      }
    }
  }
  return { table, conflicts };
}

/* ------- left recursion elimination ------- */
function eliminateLeftRecursion(prods0) {
  const prods = {};
  for (const k of Object.keys(prods0)) prods[k] = prods0[k].map(r => r.slice());

  const nonterms = Object.keys(prods);
  for (let i = 0; i < nonterms.length; i++) {
    const Ai = nonterms[i];

    for (let j = 0; j < i; j++) {
      const Aj = nonterms[j];
      const newR = [];
      for (const rhs of prods[Ai]) {
        if (rhs[0] === Aj) {
          for (const delta of prods[Aj]) {
            const comb = (delta.length === 1 && delta[0] === 'ε')
              ? rhs.slice(1)
              : delta.concat(rhs.slice(1));
            newR.push(comb.length ? comb : ['ε']);
          }
        } else newR.push(rhs);
      }
      prods[Ai] = newR;
    }

    const alphas = [], betas = [];
    for (const rhs of prods[Ai]) {
      if (rhs[0] === Ai) alphas.push(rhs.slice(1).length ? rhs.slice(1) : ['ε']);
      else betas.push(rhs);
    }
    if (alphas.length > 0) {
      let prime = Ai + "'";
      while (prods[prime]) prime += "'";
      prods[prime] = [];
      const newAi = [];
      for (const b of betas) {
        if (b.length === 1 && b[0] === 'ε') newAi.push([prime]);
        else newAi.push(b.concat([prime]));
      }
      prods[Ai] = newAi.length ? newAi : [[prime]];
      for (const a of alphas) {
        if (a.length === 1 && a[0] === 'ε') prods[prime].push([prime]);
        else prods[prime].push(a.concat([prime]));
      }
      prods[prime].push(['ε']);
      nonterms.push(prime);
    }
  }
  return prods;
}

/* ------- left factoring ------- */
function leftFactor(prods0) {
  let prods = {};
  for (const k of Object.keys(prods0)) prods[k] = prods0[k].map(r => r.slice());
  let changed = true;

  while (changed) {
    changed = false;
    for (const A of Object.keys(prods)) {
      const rhss = prods[A];
      if (rhss.length < 2) continue;

      const groups = {};
      for (const rhs of rhss) {
        const key = rhs[0] || 'ε';
        (groups[key] = groups[key] || []).push(rhs);
      }

      let factored = false;
      for (const key of Object.keys(groups)) {
        const g = groups[key];
        if (g.length <= 1) continue;

        let prefix = g[0].slice();
        for (let i = 1; i < g.length; i++) {
          const other = g[i];
          let k = 0;
          while (k < prefix.length && k < other.length && prefix[k] === other[k]) k++;
          prefix = prefix.slice(0, k);
        }
        if (prefix.length === 0) continue;

        let prime = A + "_fact";
        while (prods[prime]) prime += "_";

        const newA = [];
        const factR = [];
        for (const rhs of rhss) {
          let matches = rhs.length >= prefix.length;
          for (let i = 0; i < prefix.length && matches; i++) {
            if (rhs[i] !== prefix[i]) matches = false;
          }
          if (matches) {
            const rest = rhs.slice(prefix.length);
            factR.push(rest.length ? rest : ['ε']);
          } else newA.push(rhs);
        }
        newA.push(prefix.concat([prime]));
        prods[A] = newA;
        prods[prime] = factR;
        changed = true;
        factored = true;
        break;
      }
      if (factored) break;
    }
  }
  return prods;
}

/* ------- regex testing ------- */
function testRegex(pattern, text) {
  try {
    const re = new RegExp(pattern, 'g');
    const matches = Array.from(text.matchAll(re)).map(m => ({
      text: m[0],
      index: m.index
    }));
    return { matches };
  } catch (e) {
    return { error: e.message };
  }
}

/* ------- rendering helpers ------- */
function renderFirstFollow(prods, FIRST, FOLLOW) {
  const sym = identifySymbols(prods);
  let html = `<div style="margin-bottom:8px"><strong>Start symbol:</strong> ${escapeHtml(sym.start || '-')}</div>`;
  html += '<table class="sets"><thead><tr><th>Nonterminal</th><th>FIRST</th><th>FOLLOW</th></tr></thead><tbody>';
  for (const A of sym.nonterminals) {
    const f = Array.from(FIRST[A] || []).join(', ');
    const fo = Array.from(FOLLOW[A] || []).join(', ');
    html += `<tr><td><strong>${escapeHtml(A)}</strong></td><td>${escapeHtml(f)}</td><td>${escapeHtml(fo)}</td></tr>`;
  }
  html += '</tbody></table>';
  return html;
}
function renderTransformedGrammar(prods) {
  return `<pre style="margin:0">${escapeHtml(stringifyGrammar(prods))}</pre>`;
}
function renderPredictiveTable(table) {
  const nonterms = Object.keys(table);
  const terminals = new Set();
  for (const row of Object.values(table)) {
    for (const t of Object.keys(row)) terminals.add(t);
  }
  const termList = Array.from(terminals).sort();

  let html = '<table class="predictive"><thead><tr><th>NT \\ t</th>';
  for (const t of termList) html += `<th>${escapeHtml(t)}</th>`;
  html += '</tr></thead><tbody>';

  for (const A of nonterms) {
    html += `<tr><td><strong>${escapeHtml(A)}</strong></td>`;
    for (const t of termList) {
      const cell = table[A][t];
      if (!cell || cell.length === 0) {
        html += '<td>–</td>';
      } else {
        const txt = cell.map(r => `${A} → ${r.join(' ')}`).join('<br>');
        html += `<td>${txt}</td>`;
      }
    }
    html += '</tr>';
  }
  html += '</tbody></table>';
  return html;
}
function renderConflicts(conflicts) {
  if (!conflicts.length) {
    return '<div style="margin-top:10px;color:#16a34a;"><strong>No conflicts detected — grammar appears LL(1).</strong></div>';
  }
  let html = '<div style="margin-top:10px;color:#b91c1c;"><strong>Conflicts:</strong><br><pre style="margin-top:4px">';
  html += conflicts.map(c =>
    `NT ${c.nonterminal} on ${c.terminal}: ${c.prods.map(p => p.join(' ')).join(' || ')}`
  ).join('\n');
  html += '</pre></div>';
  return html;
}
function renderRegexHighlight(sample, matches) {
  if (!sample) return '<div class="muted">No text</div>';
  if (!matches.length) return '<div class="muted">No matches</div>';
  let last = 0, html = '';
  for (const m of matches) {
    html += escapeHtml(sample.slice(last, m.index));
    html += `<span class="match-chip">${escapeHtml(m.text)}</span>`;
    last = m.index + m.text.length;
  }
  html += escapeHtml(sample.slice(last));
  html += `<div style="margin-top:10px;color:#6b7280;">Total matches: ${matches.length}</div>`;
  return html;
}
function renderMatchList(matches) {
  if (!matches.length) return '<div class="muted">No matches</div>';
  return matches.map(m =>
    `<div class="match-item"><div>${escapeHtml(m.text)}</div><div style="color:#6b7280;">[${m.index}, ${m.index + m.text.length - 1}]</div></div>`
  ).join('');
}

/* ------- tabs wiring ------- */
const tabs = Array.from(document.querySelectorAll('.tab'));
const panels = Array.from(document.querySelectorAll('.tab-panel'));
tabs.forEach(btn => {
  btn.addEventListener('click', () => {
    tabs.forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    panels.forEach(p => p.classList.remove('active'));
    document.getElementById(btn.dataset.tab + '-panel').classList.add('active');
  });
});

/* ------- FIRST & FOLLOW handlers ------- */
document.getElementById('example-first').addEventListener('click', () => {
  document.getElementById('grammar-first').value =
`S -> A a | b
A -> A c | ε`;
  toast('Example loaded');
});
document.getElementById('compute-first').addEventListener('click', () => {
  const raw = document.getElementById('grammar-first').value.trim();
  if (!raw) { toast('Enter grammar'); return; }
  const prods = parseGrammar(raw);
  if (!Object.keys(prods).length) { toast('Could not parse grammar'); return; }
  const FIRST = computeFirst(prods);
  const FOLLOW = computeFollow(prods, FIRST, identifySymbols(prods).start);
  document.getElementById('first-output').innerHTML = renderFirstFollow(prods, FIRST, FOLLOW);
});

/* ------- Left Recursion handlers ------- */
document.getElementById('example-leftrec').addEventListener('click', () => {
  document.getElementById('grammar-leftrec').value =
`S -> S a | b
A -> A c | d`;
  toast('Example loaded');
});
document.getElementById('run-leftrec').addEventListener('click', () => {
  const raw = document.getElementById('grammar-leftrec').value.trim();
  if (!raw) { toast('Enter grammar'); return; }
  const prods = parseGrammar(raw);
  const result = eliminateLeftRecursion(prods);
  document.getElementById('leftrec-output').innerHTML = renderTransformedGrammar(result);
});

/* ------- Left Factoring handlers ------- */
document.getElementById('example-leftfact').addEventListener('click', () => {
  document.getElementById('grammar-leftfact').value =
`S -> a b c | a b d | e`;
  toast('Example loaded');
});
document.getElementById('run-leftfact').addEventListener('click', () => {
  const raw = document.getElementById('grammar-leftfact').value.trim();
  if (!raw) { toast('Enter grammar'); return; }
  const prods = parseGrammar(raw);
  const result = leftFactor(prods);
  document.getElementById('leftfact-output').innerHTML = renderTransformedGrammar(result);
});

/* ------- LL(1) handlers ------- */
document.getElementById('example-ll1').addEventListener('click', () => {
  document.getElementById('grammar-ll1').value =
`E -> T E'
E' -> + T E' | ε
T -> F T'
T' -> * F T' | ε
F -> ( E ) | id`;
  toast('Example loaded');
});
document.getElementById('run-ll1').addEventListener('click', () => {
  const raw = document.getElementById('grammar-ll1').value.trim();
  if (!raw) { toast('Enter grammar'); return; }
  const prods = parseGrammar(raw);
  if (!Object.keys(prods).length) { toast('Could not parse grammar'); return; }
  const symbols = identifySymbols(prods);
  const FIRST = computeFirst(prods);
  const FOLLOW = computeFollow(prods, FIRST, symbols.start);
  const { table, conflicts } = buildPredictiveTable(prods, FIRST, FOLLOW);

  let html = '<div><strong>FIRST & FOLLOW</strong></div>';
  html += renderFirstFollow(prods, FIRST, FOLLOW);
  html += '<div style="margin-top:12px"><strong>Predictive table</strong></div>';
  html += renderPredictiveTable(table);
  html += renderConflicts(conflicts);
  document.getElementById('ll1-output').innerHTML = html;
});

/* ------- Regex handlers ------- */
document.getElementById('example-regex').addEventListener('click', () => {
  document.getElementById('regex-pattern').value = 'a(b|c)+';
  document.getElementById('regex-text').value = 'test abc abb acbc aXc';
  toast('Example loaded');
});
document.getElementById('run-regex').addEventListener('click', () => {
  const pat = document.getElementById('regex-pattern').value.trim();
  const text = document.getElementById('regex-text').value || '';
  if (!pat) { toast('Enter regex pattern'); return; }
  const res = testRegex(pat, text);
  if (res.error) {
    document.getElementById('regex-highlight').textContent = 'Error: ' + res.error;
    document.getElementById('regex-list').innerHTML = '';
    return;
  }
  const matches = res.matches;
  document.getElementById('regex-highlight').innerHTML = renderRegexHighlight(text, matches);
  document.getElementById('regex-list').innerHTML = renderMatchList(matches);
});
