/* js/tools.js - Final Verified Compiler Toolkit */

/* =========================================
   1. UTILITIES
   ========================================= */
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
    fontSize: '13px',
    boxShadow: '0 4px 6px rgba(0,0,0,0.1)'
  });
  document.body.appendChild(el);
  setTimeout(() => el.remove(), 2000);
}

function escapeHtml(s) {
  return (s + '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}

/* =========================================
   2. TOKENIZER & PARSER
   ========================================= */

// Regex handles: ε/epsilon, Non-Terminals, Terminals, Numbers, Compound Operators (==, <=), and Punctuation
const TOKEN_RE = /ε|epsilon|[A-Z][a-zA-Z0-9_]*'*|[a-z_][a-z0-9_]*'?|[0-9]+|(==|!=|<=|>=|\|\||&&|[(){}\[\]+*\/\\^=,.:;<>|$!-])/g;

function tokenizeRHS(alt) {
  alt = (alt || '').trim();
  if (alt === '' || alt === 'ε' || alt.toLowerCase() === 'epsilon') return ['ε'];
  
  const tokens = [];
  let m;
  // Reset index to ensure fresh start for every string
  TOKEN_RE.lastIndex = 0; 
  
  while ((m = TOKEN_RE.exec(alt)) !== null) {
    const t = m[0];
    if (t.toLowerCase() === 'epsilon') tokens.push('ε');
    else tokens.push(t);
  }
  return tokens.length ? tokens : ['ε'];
}

function parseGrammar(text) {
  const lines = String(text || '').split('\n').map(l => l.trim()).filter(Boolean);
  const prods = {};
  
  for (const line of lines) {
    // Supports both -> and →
    let idx = line.indexOf('->');
    if (idx === -1) idx = line.indexOf('→');
    if (idx === -1) continue;
    
    const lhs = line.slice(0, idx).trim();
    if (!lhs) continue;
    
    const rhs = line.slice(idx + 2).trim();
    const alts = rhs.split('|').map(a => a.trim());
    
    if (!prods[lhs]) prods[lhs] = [];
    
    for (const alt of alts) {
      const toks = tokenizeRHS(alt);
      prods[lhs].push(toks);
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
        if (t === 'ε') continue;
        if (!nonterm.has(t)) terms.add(t);
      }
    }
  }
  return {
    nonterminals: Array.from(nonterm),
    terminals: Array.from(terms),
    start: Object.keys(prods)[0] || null
  };
}

/* =========================================
   3. ALGORITHMS: FIRST & FOLLOW
   ========================================= */

function firstOfString(rhs, FIRST, nonterminalsSet) {
  const res = new Set();
  let allNullable = true;

  for (const sym of rhs) {
    if (sym === 'ε') {
      res.add('ε');
      continue;
    }
    
    if (!nonterminalsSet.has(sym)) {
      res.add(sym); // Terminal
      allNullable = false;
      break;
    }
    
    // Non-terminal
    const fset = FIRST[sym] || new Set();
    for (const t of fset) {
      if (t !== 'ε') res.add(t);
    }
    
    if (!fset.has('ε')) {
      allNullable = false;
      break;
    }
  }
  
  if (allNullable) res.add('ε');
  return res;
}

function computeFirst(prods) {
  const FIRST = {};
  const nonterms = Object.keys(prods);
  const nonterminalsSet = new Set(nonterms);
  
  for (const A of nonterms) FIRST[A] = new Set();

  let changed = true;
  while (changed) {
    changed = false;
    for (const A of nonterms) {
      for (const rhs of prods[A]) {
        // Explicit Epsilon case
        if (rhs.length === 1 && rhs[0] === 'ε') {
          if (!FIRST[A].has('ε')) { FIRST[A].add('ε'); changed = true; }
          continue;
        }

        const initialSize = FIRST[A].size;
        const stringFirst = firstOfString(rhs, FIRST, nonterminalsSet);
        
        for (const t of stringFirst) {
          if (!FIRST[A].has(t)) FIRST[A].add(t);
        }
        
        if (FIRST[A].size > initialSize) changed = true;
      }
    }
  }
  return FIRST;
}

function computeFollow(prods, FIRST, startSymbol) {
  const FOLLOW = {};
  const nonterms = Object.keys(prods);
  const nonterminalsSet = new Set(nonterms);
  
  for (const A of nonterms) FOLLOW[A] = new Set();
  if (startSymbol && FOLLOW[startSymbol]) FOLLOW[startSymbol].add('$');

  let changed = true;
  while (changed) {
    changed = false;
    for (const A of nonterms) {
      for (const rhs of prods[A]) {
        for (let i = 0; i < rhs.length; i++) {
          const B = rhs[i];
          if (!nonterminalsSet.has(B)) continue;

          const beta = rhs.slice(i + 1);
          // Calculate First(beta)
          const trailer = (beta.length > 0) ? firstOfString(beta, FIRST, nonterminalsSet) : null;
          
          // Rule 1: First(beta) - {ε} -> Follow(B)
          if (trailer) {
            for (const t of trailer) {
              if (t !== 'ε' && !FOLLOW[B].has(t)) {
                FOLLOW[B].add(t);
                changed = true;
              }
            }
          }

          // Rule 2: If beta is null/nullable -> Follow(A) -> Follow(B)
          if (!trailer || trailer.has('ε')) {
            for (const t of FOLLOW[A]) {
              if (!FOLLOW[B].has(t)) {
                FOLLOW[B].add(t);
                changed = true;
              }
            }
          }
        }
      }
    }
  }
  return FOLLOW;
}

/* =========================================
   4. ALGORITHM: LL(1) TABLE
   ========================================= */

function buildPredictiveTable(prods, FIRST, FOLLOW) {
  const table = {};
  const conflicts = [];
  const nonterms = Object.keys(prods);
  const nontermSet = new Set(nonterms);
  
  // Identify all Terminals for table headers
  const terminals = new Set();
  for (const A of nonterms) {
    table[A] = {};
    for (const rhs of prods[A]) {
      for (const t of rhs) {
        if (!nontermSet.has(t) && t !== 'ε') terminals.add(t);
      }
    }
    // Include sync tokens from Follow set
    if(FOLLOW[A]) {
      for (const t of FOLLOW[A]) {
        if (t !== '$') terminals.add(t);
      }
    }
  }

  for (const A of nonterms) {
    for (const rhs of prods[A]) {
      const fs = firstOfString(rhs, FIRST, nontermSet);
      
      // 1. For terminal 'a' in First(alpha), add A -> alpha
      for (const t of fs) {
        if (t !== 'ε') {
          table[A][t] = table[A][t] || [];
          // Avoid duplicate insertion of exact same rule
          if(!table[A][t].some(r => r.join(' ') === rhs.join(' '))) {
             table[A][t].push(rhs);
          }
        }
      }
      
      // 2. If epsilon in First(alpha), add A -> alpha for 'b' in Follow(A)
      if (fs.has('ε')) {
        for (const b of FOLLOW[A]) {
          table[A][b] = table[A][b] || [];
           if(!table[A][b].some(r => r.join(' ') === rhs.join(' '))) {
             table[A][b].push(rhs);
          }
        }
      }
    }
  }

  // Detect Conflicts
  for (const A of nonterms) {
    for (const t of Object.keys(table[A])) {
      if (table[A][t].length > 1) {
        conflicts.push({ nonterminal: A, terminal: t, prods: table[A][t] });
      }
    }
  }
  
  return { table, conflicts, terminals: Array.from(terminals).sort() };
}

/* =========================================
   5. ALGORITHM: LEFT RECURSION
   ========================================= */

function eliminateLeftRecursion(prods0) {
  const prods = {};
  // Deep copy
  for (const k of Object.keys(prods0)) prods[k] = prods0[k].map(r => r.slice());
  
  const nonterms = Object.keys(prods);

  for (let i = 0; i < nonterms.length; i++) {
    const Ai = nonterms[i];
    
    // Step 1: Eliminate Indirect Recursion
    for (let j = 0; j < i; j++) {
      const Aj = nonterms[j];
      const newR = [];
      
      for (const rhs of prods[Ai]) {
        if (rhs[0] === Aj) {
          // Ai -> Aj gamma
          const gamma = rhs.slice(1);
          // Substitute Aj -> delta
          for (const delta of prods[Aj]) {
            // CORNER CASE: If delta is epsilon, result is just gamma
            let effectiveDelta = (delta.length === 1 && delta[0] === 'ε') ? [] : delta;
            
            // Combine
            let combined = effectiveDelta.concat(gamma);
            if (combined.length === 0) combined = ['ε'];
            
            newR.push(combined);
          }
        } else {
          newR.push(rhs);
        }
      }
      prods[Ai] = newR;
    }

    // Step 2: Eliminate Immediate Recursion
    const alphas = [];
    const betas = [];
    
    for (const rhs of prods[Ai]) {
      if (rhs[0] === Ai) {
        // Recursive: Ai -> Ai alpha
        const alpha = rhs.slice(1);
        alphas.push(alpha.length ? alpha : ['ε']);
      } else {
        betas.push(rhs);
      }
    }

    if (alphas.length > 0) {
      let prime = Ai + "'";
      while (prods[prime]) prime += "'";
      
      prods[prime] = [];
      const newAi = [];

      // A -> beta A'
      for (const b of betas) {
        // CORNER CASE: If beta is epsilon, result is just A'
        let cleanB = (b.length === 1 && b[0] === 'ε') ? [] : b;
        newAi.push(cleanB.concat([prime]));
      }
      prods[Ai] = newAi;

      // A' -> alpha A' | epsilon
      for (const a of alphas) {
        let cleanA = (a.length === 1 && a[0] === 'ε') ? [] : a;
        prods[prime].push(cleanA.concat([prime]));
      }
      prods[prime].push(['ε']);
      
      nonterms.push(prime); 
    }
  }
  return prods;
}

/* =========================================
   6. ALGORITHM: LEFT FACTORING
   ========================================= */

function leftFactor(prods0) {
  let prods = {};
  for (const k of Object.keys(prods0)) prods[k] = prods0[k].map(r => r.slice());
  
  let changed = true;
  while (changed) {
    changed = false;
    const nonterms = Object.keys(prods);

    for (const A of nonterms) {
      const rhss = prods[A];
      if (rhss.length < 2) continue;
      
      const groups = {};
      for (const rhs of rhss) {
        const key = rhs[0];
        (groups[key] = groups[key] || []).push(rhs);
      }

      for (const key of Object.keys(groups)) {
        const group = groups[key];
        if (group.length > 1) {
          // Find longest common prefix
          let prefix = group[0].slice();
          
          for (let i = 1; i < group.length; i++) {
            const current = group[i];
            let k = 0;
            while (k < prefix.length && k < current.length && prefix[k] === current[k]) {
              k++;
            }
            prefix = prefix.slice(0, k);
            if (prefix.length === 0) break;
          }

          if (prefix.length > 0) {
            let prime = A + "_fact";
            while (prods[prime]) prime += "_";
            
            // New A: Remove grouped items, add Prefix + Prime
            const newA = prods[A].filter(r => !group.includes(r));
            newA.push(prefix.concat([prime]));
            prods[A] = newA;

            // New Prime: The remainders
            const newPrime = [];
            for (const r of group) {
              const remainder = r.slice(prefix.length);
              // CORNER CASE: If remainder is empty (consumed by prefix), it becomes Epsilon
              newPrime.push(remainder.length ? remainder : ['ε']);
            }
            prods[prime] = newPrime;
            
            changed = true;
            break; 
          }
        }
      }
      if (changed) break;
    }
  }
  return prods;
}

/* =========================================
   7. REGEX ENGINE & MATCHING
   ========================================= */

function testRegex(pattern, text) {
  try {
    const re = new RegExp(pattern, 'g');
    // matchAll is safer/more detailed than match
    const matches = Array.from(text.matchAll(re)).map(m => ({
      text: m[0],
      index: m.index
    }));
    return { matches };
  } catch (e) {
    return { error: e.message };
  }
}

/* =========================================
   8. RENDERING HELPERS
   ========================================= */

function setPrettySet(s) {
  if (!s || s.size === 0) return '∅';
  return '{ ' + Array.from(s).join(', ') + ' }';
}

function renderFirstFollow(prods, FIRST, FOLLOW) {
  const sym = identifySymbols(prods);
  const rows = sym.nonterminals.map(A => {
    return `<tr>
      <td style="padding:8px;border-bottom:1px solid #eee"><strong>${escapeHtml(A)}</strong></td>
      <td style="padding:8px;border-bottom:1px solid #eee;color:#059669">${escapeHtml(setPrettySet(FIRST[A]))}</td>
      <td style="padding:8px;border-bottom:1px solid #eee;color:#d97706">${escapeHtml(setPrettySet(FOLLOW[A]))}</td>
    </tr>`;
  }).join('');
  
  return `<table style="width:100%;border-collapse:collapse;font-family:monospace;font-size:14px;">
    <thead><tr style="background:#f3f4f6;text-align:left">
      <th style="padding:8px">Nonterminal</th>
      <th style="padding:8px">FIRST</th>
      <th style="padding:8px">FOLLOW</th>
    </tr></thead>
    <tbody>${rows}</tbody>
  </table>`;
}

function renderTransformedGrammar(prods) {
  return `<pre style="background:#f8fafc;padding:15px;border:1px solid #e2e8f0;border-radius:6px;font-family:monospace;color:#334155">${escapeHtml(stringifyGrammar(prods))}</pre>`;
}

function renderPredictiveTable(tableObj) {
  const table = tableObj.table;
  const nonterms = Object.keys(table);
  const termList = (tableObj.terminals || []).concat(['$']);

  let html = '<div style="overflow-x:auto"><table style="width:100%;border-collapse:collapse;font-size:13px;font-family:monospace;"><thead><tr style="background:#f3f4f6">';
  html += '<th style="padding:8px;border:1px solid #e5e7eb">NT</th>';
  for (const t of termList) html += `<th style="padding:8px;border:1px solid #e5e7eb;min-width:40px">${escapeHtml(t)}</th>`;
  html += '</tr></thead><tbody>';

  for (const A of nonterms) {
    html += `<tr><td style="padding:8px;border:1px solid #e5e7eb;font-weight:bold;background:#fff">${escapeHtml(A)}</td>`;
    for (const t of termList) {
      const cell = table[A][t];
      html += '<td style="padding:8px;border:1px solid #e5e7eb;background:#fff">';
      if (cell && cell.length > 0) {
        html += cell.map(r => `<div style="white-space:nowrap;color:#2563eb">${A} → ${r.join(' ')}</div>`).join('');
      }
      html += '</td>';
    }
    html += '</tr>';
  }
  html += '</tbody></table></div>';
  return html;
}

function renderConflicts(conflicts) {
  if (!conflicts || conflicts.length === 0) {
    return '<div style="margin-top:15px;padding:12px;background:#dcfce7;color:#166534;border-radius:6px;border:1px solid #bbf7d0"><strong>✅ Grammar is LL(1). No conflicts found.</strong></div>';
  }
  let html = '<div style="margin-top:15px;padding:12px;background:#fee2e2;color:#991b1b;border-radius:6px;border:1px solid #fecaca"><strong>⚠️ Conflicts Detected (Not LL(1)):</strong><ul style="margin:5px 0 0 15px;padding:0">';
  html += conflicts.map(c => `<li>On <strong>${escapeHtml(c.nonterminal)}</strong>, input <strong>${escapeHtml(c.terminal)}</strong>: ${c.prods.map(p => escapeHtml(p.join(' '))).join(' <strong>OR</strong> ')}</li>`).join('');
  html += '</ul></div>';
  return html;
}

/* =========================================
   9. UI EVENT BINDING
   ========================================= */

document.addEventListener('DOMContentLoaded', () => {

    const get = (id) => document.getElementById(id);

    // Tab Logic
    document.querySelectorAll('.tab').forEach(btn => {
        btn.addEventListener('click', () => {
            document.querySelectorAll('.tab').forEach(b => b.classList.remove('active'));
            document.querySelectorAll('.tab-panel').forEach(p => p.classList.remove('active'));
            btn.classList.add('active');
            const p = get(btn.dataset.tab + '-panel');
            if(p) p.classList.add('active');
        });
    });

    // 1. First & Follow
    const btnExFF = get('example-first');
    if(btnExFF) btnExFF.addEventListener('click', () => {
        const el = get('grammar-first');
        if(el) el.value = "E -> T E'\nE' -> + T E' | ε\nT -> F T'\nT' -> * F T' | ε\nF -> ( E ) | id";
        toast("Example Loaded");
    });

    const btnRunFF = get('compute-first');
    if(btnRunFF) btnRunFF.addEventListener('click', () => {
        const el = get('grammar-first');
        const out = get('first-output');
        if(!el || !out) return;
        const raw = el.value.trim();
        if(!raw) return toast("Please enter a grammar");
        const prods = parseGrammar(raw);
        if(Object.keys(prods).length === 0) return toast("Invalid Grammar");
        const FIRST = computeFirst(prods);
        const FOLLOW = computeFollow(prods, FIRST, identifySymbols(prods).start);
        out.innerHTML = renderFirstFollow(prods, FIRST, FOLLOW);
    });

    // 2. Left Recursion
    const btnExLR = get('example-leftrec');
    if(btnExLR) btnExLR.addEventListener('click', () => {
        const el = get('grammar-leftrec');
        if(el) el.value = "E -> E + T | T\nT -> T * F | F\nF -> ( E ) | id";
        toast("Example Loaded");
    });

    const btnRunLR = get('run-leftrec');
    if(btnRunLR) btnRunLR.addEventListener('click', () => {
        const el = get('grammar-leftrec');
        const out = get('leftrec-output');
        if(!el || !out) return;
        const prods = parseGrammar(el.value);
        if(Object.keys(prods).length === 0) return toast("Invalid Grammar");
        const res = eliminateLeftRecursion(prods);
        out.innerHTML = renderTransformedGrammar(res);
    });

    // 3. Left Factoring
    const btnExLF = get('example-leftfact');
    if(btnExLF) btnExLF.addEventListener('click', () => {
        const el = get('grammar-leftfact');
        if(el) el.value = "S -> i E t S | i E t S e S | a\nE -> b";
        toast("Example Loaded");
    });

    const btnRunLF = get('run-leftfact');
    if(btnRunLF) btnRunLF.addEventListener('click', () => {
        const el = get('grammar-leftfact');
        const out = get('leftfact-output');
        if(!el || !out) return;
        const prods = parseGrammar(el.value);
        if(Object.keys(prods).length === 0) return toast("Invalid Grammar");
        const res = leftFactor(prods);
        out.innerHTML = renderTransformedGrammar(res);
    });

    // 4. LL(1) Table
    const btnExLL = get('example-ll1');
    if(btnExLL) btnExLL.addEventListener('click', () => {
        const el = get('grammar-ll1');
        if(el) el.value = "S -> A\nA -> a B | Ad\nB -> b\nC -> g"; 
        toast("Example (Conflict) Loaded");
    });

    const btnRunLL = get('run-ll1');
    if(btnRunLL) btnRunLL.addEventListener('click', () => {
        const el = get('grammar-ll1');
        const out = get('ll1-output');
        if(!el || !out) return;
        const prods = parseGrammar(el.value);
        if(Object.keys(prods).length === 0) return toast("Invalid Grammar");
        const FIRST = computeFirst(prods);
        const FOLLOW = computeFollow(prods, FIRST, identifySymbols(prods).start);
        const tableObj = buildPredictiveTable(prods, FIRST, FOLLOW);
        out.innerHTML = `
            <h4 style="margin:0 0 10px 0">First & Follow</h4>
            ${renderFirstFollow(prods, FIRST, FOLLOW)}
            <h4 style="margin:20px 0 10px 0">Predictive Parsing Table</h4>
            ${renderPredictiveTable(tableObj)}
            ${renderConflicts(tableObj.conflicts)}
        `;
    });

    // 5. Regex Tester
    const btnExReg = get('example-regex');
    if(btnExReg) btnExReg.addEventListener('click', () => {
        const p = get('regex-pattern');
        const t = get('regex-text');
        if(p) p.value = "a(b|c)+";
        if(t) t.value = "test abc abb acbc aXc";
        toast("Email Regex Loaded");
    });

    const btnRunReg = get('run-regex');
    if(btnRunReg) btnRunReg.addEventListener('click', () => {
        const pat = get('regex-pattern');
        const txt = get('regex-text');
        const outH = get('regex-highlight');
        const outL = get('regex-list');
        
        if(!pat || !txt || !outH) return;
        
        const textVal = txt.value;
        const res = testRegex(pat.value, textVal);
        
        if(res.error) {
            outH.innerHTML = `<div style="color:#ef4444;font-weight:bold">Error: ${res.error}</div>`;
            if(outL) outL.innerHTML = '';
            return;
        }
        
        const matches = res.matches;
        
        // Render Highlighted Text
        let html = '';
        let lastIdx = 0;
        
        if(matches.length === 0) {
            html = escapeHtml(textVal);
        } else {
            matches.forEach(m => {
                html += escapeHtml(textVal.substring(lastIdx, m.index));
                html += `<span style="background:#fde68a;color:#92400e;border-radius:2px;font-weight:bold">${escapeHtml(m.text)}</span>`;
                lastIdx = m.index + m.text.length;
            });
            html += escapeHtml(textVal.substring(lastIdx));
        }
        outH.innerHTML = `<div style="font-family:monospace;white-space:pre-wrap;background:#fff;padding:12px;border:1px solid #e5e7eb;border-radius:6px;min-height:50px">${html}</div>`;
        
        // Render Match List
        if(outL) {
            if(matches.length === 0) {
                outL.innerHTML = '<div style="color:#6b7280;margin-top:10px">No matches found.</div>';
            } else {
                const listHtml = matches.map((m, i) => `
                    <div style="display:flex;justify-content:space-between;padding:6px 10px;background:#f9fafb;border-bottom:1px solid #e5e7eb;font-size:13px;font-family:monospace">
                        <span><strong>#${i+1}</strong>: ${escapeHtml(m.text)}</span>
                        <span style="color:#6b7280">Index: ${m.index}</span>
                    </div>
                `).join('');
                
                outL.innerHTML = `
                    <div style="margin-top:15px;border:1px solid #e5e7eb;border-radius:6px;overflow:hidden">
                        <div style="background:#f3f4f6;padding:8px 10px;font-weight:bold;font-size:13px;border-bottom:1px solid #e5e7eb">Match List (${matches.length})</div>
                        <div style="max-height:150px;overflow-y:auto">${listHtml}</div>
                    </div>
                `;
            }
        }
    });
});
