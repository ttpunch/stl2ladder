import React, { useState, useEffect, useMemo, useRef, useCallback } from "react";
import { createRoot } from "react-dom/client";
import "./index.css";


/* ============================================================= *
 *  EXAMPLE STL PROGRAMS
 * ============================================================= */
const EXAMPLES = {
  motor: {
    name: "Motor Control (Full Demo)",
    code: `ORGANIZATION_BLOCK OB1
TITLE = Main Cyclic Program

NETWORK
TITLE = Motor Start / Stop with Seal-in
      A(
      O     "Start_PB"      // I0.0 momentary start
      O     "Motor_Run"     // Q0.0 seal-in contact
      )
      AN    "Stop_PB"       // I0.1 normally-closed
      =     "Motor_Run"     // Q0.0 motor contactor

NETWORK
TITLE = Set / Reset Fault Latch
      A     I0.2            // fault trip
      S     Q0.1            // latch fault lamp
      A     I0.3            // reset button
      R     Q0.1            // unlatch fault lamp

NETWORK
TITLE = On-Delay Run Timer (5s)
      A     I0.4            // enable
      L     S5T#5S          // preset 5 seconds
      SD    T1              // on-delay timer
      A     T1              // timer done bit
      =     Q0.2            // delayed output

NETWORK
TITLE = Up / Down Parts Counter
      A     I0.5            // count up pulse
      CU    C1
      A     I0.6            // count down pulse
      CD    C1
      A     C1              // count > 0
      =     Q0.3            // batch active

NETWORK
TITLE = Nested Parallel Interlock
      A(
      O     I1.0
      O     I1.1
      )
      A(
      O     I1.2
      O     I1.3
      )
      =     Q0.4

NETWORK
TITLE = Call Conveyor Function Block
      CALL  FB10, DB10

NETWORK
TITLE = Positive Edge Detection
      A     I2.0
      FP    M10.0           // edge memory bit
      =     Q0.5            // one-shot pulse

END_ORGANIZATION_BLOCK`
  },
  lamp: {
    name: "Lamp Logic (Simple)",
    code: `NETWORK
TITLE = Two-way Lamp Control
      A     "Switch_A"      // I0.0
      O     "Switch_B"      // I0.1
      AN    "Inhibit"       // I0.2
      =     "Lamp"          // Q0.0`
  },
  conveyor: {
    name: "Conveyor + Timer",
    code: `NETWORK
TITLE = Conveyor Start / Seal-in
      A(
      O     I0.0            // start
      O     Q0.0            // seal-in
      )
      AN    I0.1            // stop
      AN    I0.2            // e-stop
      =     Q0.0            // motor

NETWORK
TITLE = Off-Delay Run Lamp
      A     Q0.0
      L     S5T#10S
      SF    T2
      A     T2
      =     Q0.1`
  }
};

/* ============================================================= *
 *  TOKENIZER
 * ============================================================= */
function tokenizeLine(raw) {
  let comment = null;
  let line = raw;
  // strip block comment markers crudely
  line = line.replace(/\(\*.*?\*\)/g, "");
  const ci = line.indexOf("//");
  if (ci >= 0) { comment = line.slice(ci + 2).trim(); line = line.slice(0, ci); }
  line = line.trim();
  const tokens = [];
  let i = 0;
  while (i < line.length) {
    const c = line[i];
    if (c === " " || c === "\t") { i++; continue; }
    if (c === "(" || c === ")" || c === ",") { tokens.push(c); i++; continue; }
    if (c === '"') {
      let j = i + 1;
      while (j < line.length && line[j] !== '"') j++;
      tokens.push(line.slice(i, j + 1)); i = j + 1; continue;
    }
    // read a token; keep [...] indirect-address content (and quotes) intact
    let j = i, depth = 0, q = false;
    while (j < line.length) {
      const ch = line[j];
      if (ch === '"') q = !q;
      else if (!q && ch === "[") depth++;
      else if (!q && ch === "]") depth = Math.max(0, depth - 1);
      else if (!q && depth === 0 && " \t(),".includes(ch)) break;
      j++;
    }
    tokens.push(line.slice(i, j)); i = j;
  }
  // merge "B [AR1,P#0.0]" style: a bracketed token attaches to the preceding operand
  for (let x = tokens.length - 1; x > 0; x--) {
    if (tokens[x].startsWith("[") && !"(),".includes(tokens[x - 1])) {
      tokens[x - 1] += tokens[x]; tokens.splice(x, 1);
    }
  }
  return { tokens, comment, raw };
}

const RE = {
  blockHdr: /^(ORGANIZATION_BLOCK|FUNCTION_BLOCK|FUNCTION|DATA_BLOCK|END_ORGANIZATION_BLOCK|END_FUNCTION_BLOCK|END_FUNCTION|END_DATA_BLOCK|BEGIN|VERSION|VAR|END_VAR|STRUCT|END_STRUCT)$/i,
  operand: /^"?[IQMTCL]?\.?[IQMTC]?\d|^"|^(DB|DI|DIX|DBX|DBW|DBD|MW|MD|MB|IW|QW|IB|QB|ID|QD|PIW|PQW|FW|FB)/i,
};

const BOOL = new Set(["A","AN","O","ON","X","XN","=","S","R","FP","FN","NOT","SET","CLR","NOP"]);
const TC   = new Set(["SD","SF","SS","SP","SE","CU","CD","FR","LC","L","T"]);
const JUMP = new Set(["CALL","JC","JCN","JU","JZ","JN","JP","JM","JMZ","LOOP"]);
const TIMERS = new Set(["SD","SF","SS","SP","SE"]);
const TIMER_LABEL = { SD:"S_ODT (TON)", SF:"S_OFFDT (TOF)", SS:"S_ODTS", SP:"S_PULSE", SE:"S_PEXT" };
const COUNTER_LABEL = { CU:"S_CU (CTU)", CD:"S_CD (CTD)" };

// data-path operations that transform the accumulator -> rendered as function boxes.
// n: arity (2 = ACCU2 op ACCU1, 1 = unary on ACCU1); sym: infix symbol for binary.
const MATH_OPS = {
  "+I":{t:"ADD_I",n:2,sym:"+"}, "-I":{t:"SUB_I",n:2,sym:"−"}, "*I":{t:"MUL_I",n:2,sym:"×"}, "/I":{t:"DIV_I",n:2,sym:"÷"},
  "+D":{t:"ADD_DI",n:2,sym:"+"}, "-D":{t:"SUB_DI",n:2,sym:"−"}, "*D":{t:"MUL_DI",n:2,sym:"×"}, "/D":{t:"DIV_DI",n:2,sym:"÷"}, "MOD":{t:"MOD",n:2,sym:"mod"},
  "+R":{t:"ADD_R",n:2,sym:"+"}, "-R":{t:"SUB_R",n:2,sym:"−"}, "*R":{t:"MUL_R",n:2,sym:"×"}, "/R":{t:"DIV_R",n:2,sym:"÷"},
  "+":{t:"ADD",n:2,sym:"+"},
  "AW":{t:"AND_W",n:2,sym:"AND"}, "OW":{t:"OR_W",n:2,sym:"OR"}, "XOW":{t:"XOR_W",n:2,sym:"XOR"},
  "AD":{t:"AND_DW",n:2,sym:"AND"}, "OD":{t:"OR_DW",n:2,sym:"OR"}, "XOD":{t:"XOR_DW",n:2,sym:"XOR"},
  "NEGI":{t:"NEG_I",n:1}, "NEGD":{t:"NEG_DI",n:1}, "NEGR":{t:"NEG_R",n:1},
  "INVI":{t:"INV_I",n:1}, "INVD":{t:"INV_DI",n:1},
  "ABS":{t:"ABS",n:1}, "SQR":{t:"SQR",n:1}, "SQRT":{t:"SQRT",n:1}, "EXP":{t:"EXP",n:1}, "LN":{t:"LN",n:1},
  "SIN":{t:"SIN",n:1}, "COS":{t:"COS",n:1}, "TAN":{t:"TAN",n:1}, "ASIN":{t:"ASIN",n:1}, "ACOS":{t:"ACOS",n:1}, "ATAN":{t:"ATAN",n:1},
  "BTI":{t:"BCD→INT",n:1}, "ITB":{t:"INT→BCD",n:1}, "BTD":{t:"BCD→DINT",n:1}, "ITD":{t:"INT→DINT",n:1},
  "DTB":{t:"DINT→BCD",n:1}, "DTR":{t:"DINT→REAL",n:1}, "RND":{t:"ROUND",n:1}, "TRUNC":{t:"TRUNC",n:1}, "RND+":{t:"CEIL",n:1}, "RND-":{t:"FLOOR",n:1},
  "SLW":{t:"SHL_W",n:1,sh:true}, "SRW":{t:"SHR_W",n:1,sh:true}, "SLD":{t:"SHL_DW",n:1,sh:true}, "SRD":{t:"SHR_DW",n:1,sh:true},
  "SSI":{t:"SHR_I±",n:1,sh:true}, "SSD":{t:"SHR_DI±",n:1,sh:true}, "RLD":{t:"ROL_DW",n:1,sh:true}, "RRD":{t:"ROR_DW",n:1,sh:true}, "RLDA":{t:"ROL_A",n:1,sh:true}, "RRDA":{t:"ROR_A",n:1,sh:true},
};
// jump / loop family
const JUMP_OPS = new Set(["JU","JC","JCN","JCB","JNB","JBI","JNBI","JO","JOS","JZ","JN","JP","JM","JPZ","JMZ","JUO","JL","LOOP"]);
// every recognized STL mnemonic -> never reported as "unrecognized"
const STL_KNOWN = new Set([
  "A","AN","O","ON","X","XN","NOT","SET","CLR","SAVE","=","R","S","FP","FN","NEG","POS",
  "L","LC","T","TAK","PUSH","POP","ENT","LEAVE","INC","DEC","BLD","NOP",
  "SP","SE","SD","SS","SF","FR","CU","CD",
  "MOD","CAW","CAD","CALL","CC","UC",
  "LAR1","LAR2","TAR1","TAR2","LAR","TAR","CAR","+AR1","+AR2","+AR","TAW","TAD",
  "OPN","OPNDI","CDB","BE","BEU","BEC","MCR","MCRA","MCRD",
  ...Object.keys(MATH_OPS), ...JUMP_OPS,
]);

/* ============================================================= *
 *  PARSER  ->  networks -> rungs -> RungNode tree
 * ============================================================= */
function parseProgram(text) {
  const lines = text.split("\n");
  const networks = [];
  let cur = null;
  let blockType = null, blockName = null;
  let netCounter = 0;
  const globalErrors = [];

  function newNetwork(num, title) {
    cur = { number: num, title: title || "", instrs: [] };
    networks.push(cur);
  }

  for (let li = 0; li < lines.length; li++) {
    const { tokens, comment, raw } = tokenizeLine(lines[li]);
    if (tokens.length === 0) continue;
    const head = tokens[0];

    if (/^NETWORK$/i.test(head)) {
      netCounter++;
      const num = tokens[1] && /^\d+$/.test(tokens[1]) ? parseInt(tokens[1]) : netCounter;
      newNetwork(num, "");
      continue;
    }
    if (/^TITLE$/i.test(head)) {
      const eq = raw.indexOf("=");
      const title = eq >= 0 ? raw.slice(eq + 1).trim() : "";
      if (cur) cur.title = title; else { blockName = blockName || ""; }
      continue;
    }
    if (RE.blockHdr.test(head)) {
      if (/ORGANIZATION_BLOCK/i.test(head)) { blockType = "OB"; blockName = tokens[1] || ""; }
      else if (/FUNCTION_BLOCK/i.test(head)) { blockType = "FB"; blockName = tokens[1] || ""; }
      else if (/^FUNCTION$/i.test(head)) { blockType = "FC"; blockName = tokens[1] || ""; }
      else if (/DATA_BLOCK/i.test(head)) { blockType = "DB"; blockName = tokens[1] || ""; }
      continue;
    }
    // instruction line
    if (!cur) newNetwork(++netCounter, "");
    cur.instrs.push({ tokens, comment, raw, lineNo: li + 1 });
  }

  const parsedNets = networks.map(parseNetwork).filter(Boolean);
  return { blockType, blockName, networks: parsedNets, globalErrors };
}

const seriesOf = (list) => {
  const c = list.filter(Boolean);
  if (c.length === 0) return null;
  if (c.length === 1) return c[0];
  return { type: "SERIES", children: c };
};
const orReduce = (list) => {
  const c = list.filter(Boolean);
  if (c.length === 0) return null;
  if (c.length === 1) return c[0];
  return { type: "PARALLEL", children: c };
};

function parseNetwork(net) {
  const rungs = [];
  const warnings = [];
  let frames = [{ or: [], cur: [] }];
  let opStack = [];
  let lastLoad = null;
  let bracketDepth = 0;

  const top = () => frames[frames.length - 1];
  const startOrTerm = () => { top().or.push(seriesOf(top().cur)); top().cur = []; };
  const currentLogic = () => {
    // collapse any unclosed frames defensively
    let logic = orReduce(top().or.concat([seriesOf(top().cur)]));
    return logic;
  };
  const resetVKE = () => { frames = [{ or: [], cur: [] }]; opStack = []; lastLoad = null; accu1 = null; accu2 = null; accuOp = null; };
  const contact = (kind, operand, comment) => ({ type: "CONTACT", kind, operand: operand || "??", negated: kind === "NC", comment: comment || null });

  let pendingOutputs = [];
  let emitted = false; // true after a write op; the next bit-logic instruction starts a new rung
  // lightweight accumulator model for the data path (L / math / T -> function boxes)
  let accu1 = null, accu2 = null, accuOp = null; // accuOp = title of the op that produced accu1, or null (plain value)

  function flushRung() {
    if (pendingOutputs.length) {
      rungs.push({ logic: currentLogic(), outputs: pendingOutputs, warnings: [] });
    }
    pendingOutputs = [];
    resetVKE();
    emitted = false;
  }
  // a bit-logic instruction is starting; if outputs were already written, that begins a NEW rung
  function beginLogic() { if (emitted) flushRung(); }
  // S7 VKE persists across consecutive writes -> attach to the SAME rung's output list
  function addOutput(output, comment) {
    if (comment && !output.comment) output.comment = comment;
    pendingOutputs.push(output);
    emitted = true;
  }

  for (const instr of net.instrs) {
    let t = instr.tokens.filter(x => x !== ",");
    // strip a leading jump label "NAME:" (e.g. LOOP1:) — it marks a jump target, not an instruction
    if (t[0] && /^[A-Za-z_]\w*:$/.test(t[0])) t = t.slice(1);
    let m = t[0];
    if (!m) continue;
    const mUpper = m.toUpperCase();
    const operand = t[1];

    // any bit-logic instruction (or a bare "(") begins a logic string; if outputs were
    // just written, that starts a new rung (VKE persists only across writes, not logic).
    if (["A","AN","O","ON","X","XN"].includes(mUpper) || m === "(") beginLogic();

    // bracket opens: A( O( AN( ON(
    if ((mUpper === "A" || mUpper === "AN" || mUpper === "O" || mUpper === "ON") && t[1] === "(") {
      const op = (mUpper === "O" || mUpper === "ON") ? "OR" : "AND";
      frames.push({ or: [], cur: [] }); opStack.push(op); bracketDepth++;
      continue;
    }
    if (m === "(") { frames.push({ or: [], cur: [] }); opStack.push("AND"); bracketDepth++; continue; }
    if (m === ")") {
      if (frames.length <= 1) { warnings.push("Unbalanced ')' in network " + net.number); continue; }
      const f = frames.pop(); bracketDepth--;
      const node = orReduce(f.or.concat([seriesOf(f.cur)]));
      const op = opStack.pop();
      if (op === "OR") { startOrTerm(); top().cur.push(node); }
      else { top().cur.push(node); }
      continue;
    }

    const cmt = instr.comment;
    switch (mUpper) {
      case "A":  top().cur.push(contact("NO", operand, cmt)); break;
      case "AN": top().cur.push(contact("NC", operand, cmt)); break;
      case "X":  top().cur.push(contact("XOR", operand, cmt)); break;
      case "XN": top().cur.push({ ...contact("XOR", operand, cmt), xn:true }); break;
      case "O":
        if (!operand) { startOrTerm(); }
        else { startOrTerm(); top().cur.push(contact("NO", operand, cmt)); }
        break;
      case "ON":
        if (!operand) { startOrTerm(); }
        else { startOrTerm(); top().cur.push(contact("NC", operand, cmt)); }
        break;
      case "=":  addOutput({ kind: "COIL", operand }, cmt); break;
      case "S":  addOutput({ kind: "SET", operand }, cmt); break;
      case "R":  addOutput({ kind: "RESET", operand }, cmt); break;
      // FP/FN are inline edge detectors in the VKE chain (memory bit = operand),
      // not output coils — render as ─┤P├─ / ─┤N├─ contacts in series.
      case "FP": top().cur.push(contact("PEDGE", operand, cmt)); break;
      case "FN": top().cur.push(contact("NEDGE", operand, cmt)); break;
      case "SD": case "SF": case "SS": case "SP": case "SE":
        addOutput({ kind: "TIMER", timerType: mUpper, operand, preset: lastLoad }, cmt); break;
      case "CU": case "CD":
        addOutput({ kind: "COUNTER", counterType: mUpper, operand, preset: lastLoad }, cmt); break;
      case "L": case "LC":
        accu2 = accu1; accu1 = disp(operand); accuOp = null; lastLoad = operand; break;
      case "T":
        if (accuOp) addOutput({ kind: "FUNC", title: accuOp, expr: accu1, dst: disp(operand) }, cmt);
        else addOutput({ kind: "MOVE", src: accu1 || lastLoad || "ACCU", dst: disp(operand) }, cmt);
        accu1 = null; accu2 = null; accuOp = null;
        break;
      case "CALL": case "CC": case "UC": {
        const parts = t.slice(1);
        addOutput({ kind: "FBCALL", fb: parts[0] || "FB", db: parts[1] || "" }, cmt);
        break;
      }
      case "FR":
        addOutput({ kind: "BOX", title: "FR", operand }, cmt); break;
      case "NOT":
        top().cur.push({ type: "CONTACT", kind: "NOT", operand: "NOT" }); break;
      case "OPN": case "OPNDI": case "CDB":
        // open data block — sets DB context, no ladder element
        break;
      case "SET": case "CLR": case "NOP": case "SAVE":
        break;
      case "BLD": case "BE": case "BEU": case "BEC": case "TAK": case "PUSH": case "POP": case "ENT": case "LEAVE":
        break;
      default:
        if (MATH_OPS[mUpper]) {
          // data-path math/logic/convert/shift — transform the accumulator expression
          const meta = MATH_OPS[mUpper];
          if (meta.n === 2) accu1 = `${accu2 ?? "ACCU2"} ${meta.sym} ${accu1 ?? "ACCU1"}`;
          else if (meta.sh) accu1 = `${meta.t}(${accu1 ?? "ACCU1"}${operand ? ", " + disp(operand) : ""})`;
          else accu1 = `${meta.t}(${accu1 ?? "ACCU1"})`;
          accuOp = meta.t;
        } else if (JUMP_OPS.has(mUpper)) {
          addOutput({ kind: "JUMP", op: mUpper, label: operand }, cmt);
        } else if (/^(==|<>|>=|<=|>|<)[IDR]?$/.test(m) || /^[<>=!]=?[IDR]$/.test(m)) {
          // comparators like >=I  ==I etc
          top().cur.push({ type: "CONTACT", kind: "COMPARE", operand: m });
        } else if (STL_KNOWN.has(mUpper)) {
          // recognized STL op with no distinct ladder element (accumulator / control / register)
          break;
        } else {
          warnings.push(`Network ${net.number}: unrecognized instruction "${m}".`);
        }
    }
  }

  // flush the final rung, or emit leftover logic that never got an output
  if (pendingOutputs.length) {
    flushRung();
  } else if (top().or.length || top().cur.length) {
    rungs.push({ logic: currentLogic(), outputs: [], warnings: ["No output assignment (incomplete rung)."] });
  }
  if (bracketDepth !== 0) warnings.push(`Network ${net.number}: unbalanced brackets.`);

  if (rungs.length === 0) return null;
  const hasUnsupported = warnings.length > 0 || rungs.some(r => r.outputs.some(o => o.kind === "JUMP"));
  return { number: net.number, title: net.title, rungs, warnings, hasUnsupported };
}

/* ============================================================= *
 *  SVG LAYOUT
 * ============================================================= */
const SYM = 82, BOX_W = 140, BOX_H = 86, LANE_H = 94, RAIL_L = 46, NET_HDR = 74;

function measure(n) {
  if (!n) return { w: 70, lanes: 1 };
  if (n.type === "CONTACT") return { w: SYM, lanes: 1 };
  if (n.type === "SERIES") {
    let w = 0, l = 1;
    n.children.forEach(c => { const m = measure(c); w += m.w; l = Math.max(l, m.lanes); });
    return { w, lanes: l };
  }
  if (n.type === "PARALLEL") {
    let w = 0, l = 0;
    n.children.forEach(c => { const m = measure(c); w = Math.max(w, m.w); l += m.lanes; });
    return { w, lanes: l };
  }
  return { w: SYM, lanes: 1 };
}

function Ladder({ networks, themeKey, zoom = 1, xlate }) {
  const tr = (c) => (xlate && c && xlate[c]) ? xlate[c] : c;
  // first pass: compute width needed per rung
  const layout = useMemo(() => {
    const rows = [];
    networks.forEach(net => {
      net.rungs.forEach((rung, ri) => {
        const m = measure(rung.logic);
        const anyBox = (rung.outputs || []).some(o => ["TIMER","COUNTER","FBCALL","MOVE","JUMP","BOX","FUNC"].includes(o.kind));
        const outW = anyBox ? BOX_W : SYM;
        const need = RAIL_L + 12 + m.w + 50 + outW + 12 + RAIL_L;
        rows.push({ net, rung, ri, mw: m.w, lanes: m.lanes, outW, need });
      });
    });
    const width = Math.max(640, ...rows.map(r => r.need), 0);
    return { rows, width };
  }, [networks]);

  // build elements
  const els = [];
  let key = 0;
  const k = () => "e" + (key++);
  let y = 14;
  const width = layout.width;
  const rightRailX = width - RAIL_L;

  // render the extracted absolute address (if hidden in a symbol) and the description
  function drawIODetail(operand, comment, cx, yy) {
    const { name, addr, detail } = splitComment(operand, comment);
    let y2 = yy;
    if (addr && addr !== name) {
      els.push(<text key={k()} className={addrClass(addr)} x={cx} y={y2} textAnchor="middle">{addr}</text>);
      y2 += 13;
    }
    if (detail) {
      els.push(<text key={k()} className="opcomment" x={cx} y={y2} textAnchor="middle">{trunc(detail, 24)}</text>);
    }
  }

  function drawContact(n, x, cy) {
    const b1 = x + 26, b2 = x + 54, tp = cy - 16, bt = cy + 16;
    els.push(<line key={k()} className="wire" x1={x} y1={cy} x2={b1} y2={cy} />);
    els.push(<line key={k()} className="wire" x1={b2} y1={cy} x2={x + SYM} y2={cy} />);
    if (n.kind === "COMPARE" || n.kind === "NOT") {
      els.push(<rect key={k()} className="boxrect" x={x+18} y={cy-18} width={SYM-36} height={36} rx="3" />);
      els.push(<text key={k()} className="symtext" x={x+SYM/2} y={cy+4} textAnchor="middle">{n.operand}</text>);
      drawIODetail(n.operand, tr(n.comment), x+SYM/2, cy+32);
      return;
    }
    els.push(<line key={k()} className="contact" x1={b1} y1={tp} x2={b1} y2={bt} />);
    els.push(<line key={k()} className="contact" x1={b2} y1={tp} x2={b2} y2={bt} />);
    if (n.kind === "NC") els.push(<line key={k()} className="contact" x1={b1-5} y1={bt} x2={b2+5} y2={tp} />);
    if (n.kind === "XOR") els.push(<text key={k()} className="symtext" x={(b1+b2)/2} y={cy+5} textAnchor="middle">{n.xn ? "X̄" : "X"}</text>);
    if (n.kind === "PEDGE" || n.kind === "NEDGE") els.push(<text key={k()} className="symtext" x={(b1+b2)/2} y={cy+5} textAnchor="middle">{n.kind === "PEDGE" ? "P" : "N"}</text>);
    const nm = disp(n.operand);
    els.push(<text key={k()} className={isAddr(nm) ? addrClass(nm) : "operand"} x={(b1+b2)/2} y={tp-8} textAnchor="middle">{nm}</text>);
    drawIODetail(n.operand, tr(n.comment), (b1+b2)/2, cy+32);
  }

  function renderNode(n, x, cy) {
    if (!n) { els.push(<line key={k()} className="wire" x1={x} y1={cy} x2={x+70} y2={cy} />); return x+70; }
    if (n.type === "CONTACT") { drawContact(n, x, cy); return x + SYM; }
    if (n.type === "SERIES") { let cx = x; n.children.forEach(c => { cx = renderNode(c, cx, cy); }); return cx; }
    if (n.type === "PARALLEL") {
      const m = measure(n); const bw = m.w;
      let laneTop = cy - (m.lanes * LANE_H) / 2;
      const centers = [];
      n.children.forEach(c => {
        const cm = measure(c);
        const ccy = laneTop + (cm.lanes * LANE_H) / 2;
        centers.push(ccy);
        const xe = renderNode(c, x, ccy);
        if (xe < x + bw) els.push(<line key={k()} className="wire" x1={xe} y1={ccy} x2={x+bw} y2={ccy} />);
        laneTop += cm.lanes * LANE_H;
      });
      const yT = centers[0], yB = centers[centers.length-1];
      els.push(<line key={k()} className="wire" x1={x} y1={yT} x2={x} y2={yB} />);
      els.push(<line key={k()} className="wire" x1={x+bw} y1={yT} x2={x+bw} y2={yB} />);
      return x + bw;
    }
    return x;
  }

  function drawCoil(out, x, cy) {
    const a = x + 26, b = x + 56;
    els.push(<line key={k()} className="wire" x1={x} y1={cy} x2={a} y2={cy} />);
    els.push(<line key={k()} className="wire" x1={b} y1={cy} x2={x+SYM} y2={cy} />);
    const sr = out.kind !== "COIL";
    const cls = sr ? "coil-sr" : "coil";
    els.push(<path key={k()} className={cls} d={`M ${a} ${cy-17} Q ${a-13} ${cy} ${a} ${cy+17}`} />);
    els.push(<path key={k()} className={cls} d={`M ${b} ${cy-17} Q ${b+13} ${cy} ${b} ${cy+17}`} />);
    const letter = { SET:"S", RESET:"R", PEDGE:"P", NEDGE:"N" }[out.kind];
    if (letter) els.push(<text key={k()} className={sr?"coiltext-sr":"coiltext"} x={(a+b)/2} y={cy+5} textAnchor="middle">{letter}</text>);
    const nm = disp(out.operand);
    els.push(<text key={k()} className={isAddr(nm) ? addrClass(nm) : "operand"} x={(a+b)/2} y={cy-24} textAnchor="middle">{nm}</text>);
    drawIODetail(out.operand, tr(out.comment), (a+b)/2, cy+32);
  }

  function drawBox(out, x, cy) {
    const bx = x + 14, bw = BOX_W - 28, top = cy - BOX_H/2;
    els.push(<line key={k()} className="wire" x1={x} y1={cy} x2={bx} y2={cy} />);
    els.push(<line key={k()} className="wire" x1={bx+bw} y1={cy} x2={x+BOX_W} y2={cy} />);
    let title = "", lines = [];
    if (out.kind === "TIMER") { title = out.operand || "T?"; lines = [TIMER_LABEL[out.timerType]||out.timerType, out.preset ? "PT "+disp(out.preset) : ""]; }
    else if (out.kind === "COUNTER") { title = out.operand || "C?"; lines = [COUNTER_LABEL[out.counterType]||out.counterType, out.counterType==="CU"?"count up":"count down"]; }
    else if (out.kind === "FBCALL") { title = "CALL"; lines = [out.fb, out.db ? "DB "+out.db : ""]; }
    else if (out.kind === "MOVE") { title = "MOVE"; lines = ["IN "+disp(out.src), "OUT "+disp(out.dst)]; }
    else if (out.kind === "FUNC") { title = out.title; lines = [trunc(out.expr, 16), "= "+disp(out.dst)]; }
    else if (out.kind === "JUMP") { title = out.op; lines = ["→ "+(disp(out.label)||"label"), "(control)"]; }
    else { title = out.title || "BOX"; lines = [disp(out.operand)]; }
    const jump = out.kind === "JUMP";
    els.push(<rect key={k()} className={jump?"jumpbox":"boxrect"} x={bx} y={top} width={bw} height={BOX_H} rx="5" />);
    els.push(<line key={k()} className={jump?"jumpbox":"boxrect"} x1={bx} y1={top+22} x2={bx+bw} y2={top+22} style={{fill:"none"}} />);
    els.push(<text key={k()} className="boxtitle" x={bx+bw/2} y={top+16} textAnchor="middle">{title}</text>);
    lines.filter(Boolean).forEach((ln, i) => {
      els.push(<text key={k()} className="boxtext" x={bx+bw/2} y={top+40+i*18} textAnchor="middle">{ln}</text>);
    });
    drawIODetail(out.operand || out.dst || out.label, tr(out.comment), bx+bw/2, top+BOX_H+14);
  }

  networks.forEach(net => {
    // gather inputs (reads) and outputs (writes) for this network
    const ins = [], outs = [], seenI = new Set(), seenO = new Set();
    const collect = (node) => {
      if (!node) return;
      if (node.type === "CONTACT") {
        if (node.operand && !["NOT","COMPARE"].includes(node.kind)) {
          const r = splitComment(node.operand, tr(node.comment)); const a = r.addr || r.name;
          if (a && !seenI.has(a)) { seenI.add(a); ins.push(a); }
        }
        return;
      }
      (node.children || []).forEach(collect);
    };
    net.rungs.forEach(r => {
      collect(r.logic);
      (r.outputs || []).forEach(o => {
        const tgt = o.operand || o.dst || o.fb;
        const r2 = splitComment(tgt, tr(o.comment)); const a = r2.addr || r2.name;
        if (a && !seenO.has(a)) { seenO.add(a); outs.push(a); }
      });
    });

    // network header — colored per network (mirrors the editor gutter/header color)
    const nc = netColor(net.number) || "var(--accent)";
    els.push(<line key={k()} x1={10} y1={y} x2={width-10} y2={y} style={{ stroke: nc, strokeWidth: 1.5, strokeDasharray: "4 4", opacity: 0.5 }} />);
    els.push(<rect key={k()} x={10} y={y+8} width={6} height={NET_HDR-14} rx={3} style={{ fill: nc }} />);
    els.push(<text key={k()} x={26} y={y+22} style={{ fill: nc, fontFamily: "Inter", fontSize: "13px", fontWeight: 700 }}>{"NETWORK " + net.number}</text>);
    if (net.title) els.push(<text key={k()} className="netsub" x={26} y={y+39}>{net.title}</text>);
    if (net.hasUnsupported) els.push(<text key={k()} className="netsub" x={width-16} y={y+22} textAnchor="end" style={{fill:"var(--amber)"}}>⚠ contains annotations</text>);
    if (ins.length) els.push(<text key={k()} className="iolab-i" x={26} y={y+59}>{"IN ▸ " + trunc(ins.join(", "), 52)}</text>);
    if (outs.length) els.push(<text key={k()} className="iolab-q" x={width-16} y={y+59} textAnchor="end">{"OUT ▸ " + trunc(outs.join(", "), 40)}</text>);
    y += NET_HDR;

    net.rungs.forEach(rung => {
      const m = measure(rung.logic);
      const outputs = rung.outputs || [];
      const isBox = (o) => ["TIMER","COUNTER","FBCALL","MOVE","JUMP","BOX","FUNC"].includes(o.kind);
      const anyBox = outputs.some(isBox);
      const outW = anyBox ? BOX_W : SYM;
      const laneCount = Math.max(m.lanes, Math.max(1, outputs.length));
      const h = laneCount * LANE_H;
      const cy = y + h/2;

      // rails — colored per network
      els.push(<line key={k()} x1={RAIL_L} y1={y+6} x2={RAIL_L} y2={y+h-6} style={{ stroke: nc, strokeWidth: 3 }} />);
      els.push(<line key={k()} x1={rightRailX} y1={y+6} x2={rightRailX} y2={y+h-6} style={{ stroke: nc, strokeWidth: 3 }} />);

      // logic
      const xStart = RAIL_L + 12;
      els.push(<line key={k()} className="wire" x1={RAIL_L} y1={cy} x2={xStart} y2={cy} />);
      const xEnd = renderNode(rung.logic, xStart, cy);

      // outputs — one or more coils/boxes that share this rung's VKE, stacked vertically
      const xOut = rightRailX - outW;
      if (outputs.length === 0) {
        els.push(<line key={k()} className="wire" x1={xEnd} y1={cy} x2={rightRailX} y2={cy} />);
      } else {
        const N = outputs.length;
        const centers = outputs.map((_, i) => (cy - N * LANE_H / 2) + (i + 0.5) * LANE_H);
        const branchX = xOut - 22;
        els.push(<line key={k()} className="wire" x1={xEnd} y1={cy} x2={branchX} y2={cy} />);
        if (N > 1) els.push(<line key={k()} className="wire" x1={branchX} y1={centers[0]} x2={branchX} y2={centers[N-1]} />);
        outputs.forEach((o, i) => {
          const ocy = N > 1 ? centers[i] : cy;
          const ow = isBox(o) ? BOX_W : SYM;
          els.push(<line key={k()} className="wire" x1={branchX} y1={ocy} x2={xOut} y2={ocy} />);
          if (isBox(o)) drawBox(o, xOut, ocy); else drawCoil(o, xOut, ocy);
          els.push(<line key={k()} className="wire" x1={xOut + ow} y1={ocy} x2={rightRailX} y2={ocy} />);
        });
      }
      y += h;
    });
    y += 10;
  });

  const height = y + 14;

  return (
    <svg id="ladderSvg" xmlns="http://www.w3.org/2000/svg"
         viewBox={`0 0 ${width} ${height}`} width={width} height={height}
         style={{ background: "transparent", display: "block", width: width * zoom, height: height * zoom }}>
      {els}
    </svg>
  );
}

function disp(op) {
  if (op == null) return "";
  return String(op).replace(/^"|"$/g, "");
}
function trunc(s, n) { s = String(s || ""); return s.length > n ? s.slice(0, n - 1) + "…" : s; }
function isAddr(s) {
  return /^(I|Q|M|T|C)\d/i.test(s) || /^(IB|IW|ID|QB|QW|QD|MB|MW|MD)\d/i.test(s) || /^DB\d/i.test(s) || /^DB\d+\.DB[XBWD]/i.test(s);
}
// split an operand + its inline comment into { name, addr, detail }
function splitComment(operand, comment) {
  const name = disp(operand);
  let addr = isAddr(name) ? name : null;
  let detail = (comment || "").trim();
  if (!addr && detail) {
    const m = detail.match(/^((?:I|Q|M)\s?\d+\.\d+|(?:I|Q|M)[BWD]\d+|[TC]\d+|MD\d+|DB\d+(?:\.DB[XBWD]\d+(?:\.\d+)?)?)\b[\s:.–\-]*/i);
    if (m) { addr = m[1].replace(/\s+/g, ""); detail = detail.slice(m[0].length).trim(); }
  }
  return { name, addr, detail };
}
function addrClass(a) {
  if (!a) return "addr-m";
  if (/^I/i.test(a)) return "addr-i";
  if (/^Q/i.test(a)) return "addr-q";
  if (/^[TC]\d/i.test(a)) return "addr-tc";
  return "addr-m";
}

/* ============================================================= *
 *  NETWORK COLOR CODING — each NETWORK gets a distinct hue,
 *  mirrored in the editor (gutter + headers) and the ladder
 *  (network header + power rails) so STL <-> ladder map by color.
 * ============================================================= */
const NET_PALETTE = ["#38bdf8", "#f59e0b", "#34d399", "#a78bfa", "#fb7185", "#22d3ee", "#f472b6", "#4ade80", "#fbbf24", "#818cf8"];
function netColor(n) {
  if (!n || n < 1) return null;
  const len = NET_PALETTE.length;
  return NET_PALETTE[((n - 1) % len + len) % len];
}
// map each source line index -> network number (0 = preamble before first NETWORK)
function lineNetworkMap(code) {
  const out = []; let n = 0;
  for (const l of String(code).split("\n")) { if (/^\s*NETWORK\b/i.test(l)) n++; out.push(n); }
  return out;
}

/* ============================================================= *
 *  TRANSLATION (comments -> English) — uses free public endpoints
 * ============================================================= */
function looksEnglish(s) {
  // heuristic: any non-ASCII char (accents, CJK, Cyrillic, ...) => assume non-English and translate.
  const t = String(s || "").trim();
  if (!t) return true;
  return !/[^\x00-\x7F]/.test(t);
}
async function translateOne(text) {
  const q = String(text || "").trim();
  if (!q) return text;
  // 1) unofficial google endpoint
  try {
    const r = await fetch("https://translate.googleapis.com/translate_a/single?client=gtx&sl=auto&tl=en&dt=t&q=" + encodeURIComponent(q));
    if (r.ok) {
      const j = await r.json();
      if (Array.isArray(j) && Array.isArray(j[0])) return j[0].map(seg => seg[0]).join("").trim();
    }
  } catch (e) {}
  // 2) MyMemory fallback
  try {
    const r = await fetch("https://api.mymemory.translated.net/get?q=" + encodeURIComponent(q) + "&langpair=auto|en");
    if (r.ok) { const j = await r.json(); if (j && j.responseData && j.responseData.translatedText) return j.responseData.translatedText.trim(); }
  } catch (e) {}
  return null; // signal failure
}

/* ============================================================= *
 *  OCR (image -> STL text) — lazy-loads Tesseract.js from CDN
 * ============================================================= */
let _tessPromise = null;
function loadTesseract() {
  if (window.Tesseract) return Promise.resolve(window.Tesseract);
  if (_tessPromise) return _tessPromise;
  _tessPromise = new Promise((res, rej) => {
    const s = document.createElement("script");
    s.src = "https://unpkg.com/tesseract.js@5/dist/tesseract.min.js";
    s.onload = () => res(window.Tesseract);
    s.onerror = () => rej(new Error("Could not load OCR engine (offline?)"));
    document.head.appendChild(s);
  });
  return _tessPromise;
}
// light clean-up of OCR output to better resemble S7 STL
function cleanOcrStl(raw) {
  return String(raw || "")
    .split("\n")
    .map(line => line.replace(/[ \t]+$/g, ""))
    .join("\n")
    .replace(/‘|’/g, "'")
    .replace(/“|”/g, '"')
    .replace(/[|]{2,}/g, "")     // stray OCR pipes
    .replace(/\n{3,}/g, "\n\n")
    .trim();
}

/* ============================================================= *
 *  SYNTAX HIGHLIGHT
 * ============================================================= */
function classify(tok) {
  if (RE.blockHdr.test(tok) || /^(NETWORK|TITLE|END_NETWORK)$/i.test(tok)) return "t-block";
  if (JUMP.has(tok.toUpperCase())) return "t-jump";
  if (TC.has(tok.toUpperCase())) return "t-tc";
  if (BOOL.has(tok.toUpperCase())) return "t-bool";
  if (/^(S5T#|T#|C#|B#|W#|DW#|L#|P#)/i.test(tok)) return "t-num";
  if (/^[-+]?\d/.test(tok)) return "t-num";
  if (/^"/.test(tok)) return "t-operand";
  if (/^(I|Q|M|T|C|DB|DI|MW|MD|MB|IW|QW|IB|QB|ID|QD|PIW|PQW|FW|FB|DBX|DBW|DBD|DIX)/i.test(tok) && /[\d.]/.test(tok)) return "t-operand";
  if (/^(I|Q|M|T|C)\d/i.test(tok)) return "t-operand";
  return "";
}

/* ============================================================= *
 *  STL POINTERS & INDIRECT ADDRESSING — help reference
 * ============================================================= */
const POINTER_REF = [
  {
    group: "Address registers",
    items: [
      { mn: "AR1", name: "Address Register 1", desc: "32-bit address register used for register-indirect addressing. Holds an area-internal or area-crossing pointer.", ex: "A   I[AR1,P#0.0]" },
      { mn: "AR2", name: "Address Register 2", desc: "Second address register. The compiler uses AR2 to address multi-instance / FB instance-DB data.", ex: "L   DBW[AR2,P#4.0]" },
    ],
  },
  {
    group: "Load / transfer address registers",
    items: [
      { mn: "LAR1", name: "Load AR1", desc: "Load AR1 with a pointer — from ACCU 1 (no operand) or directly from a pointer / doubleword source.", ex: "LAR1  P#10.0     LAR1  MD20" },
      { mn: "LAR2", name: "Load AR2", desc: "Load AR2 with a pointer (from ACCU 1 or a source).", ex: "LAR2  P#0.0" },
      { mn: "TAR1", name: "Transfer AR1", desc: "Store AR1 to ACCU 1 (no operand) or to a doubleword destination.", ex: "TAR1  MD24" },
      { mn: "TAR2", name: "Transfer AR2", desc: "Store AR2 to ACCU 1 or to a destination.", ex: "TAR2  MD28" },
      { mn: "CAR", name: "Exchange AR1 ↔ AR2", desc: "Swap the contents of the two address registers.", ex: "CAR" },
      { mn: "+AR1", name: "Add to AR1", desc: "Add ACCU 1 (or a P# offset) to AR1 — used to step a pointer through an array / field.", ex: "+AR1  P#2.0" },
      { mn: "+AR2", name: "Add to AR2", desc: "Add ACCU 1 (or a P# offset) to AR2.", ex: "+AR2" },
    ],
  },
  {
    group: "Pointer literals (P#)",
    items: [
      { mn: "P#b.b", name: "Area-internal pointer", desc: "Pointer constant as byte.bit within the implied area. Loaded into an AR or a doubleword.", ex: "L   P#8.0" },
      { mn: "P#area", name: "Area-crossing pointer", desc: "32-bit pointer that also carries the memory area (I/Q/M/…), so one pointer can reach several areas.", ex: "L   P#M10.0     L   P#I0.0" },
      { mn: "P#DBx.DBX", name: "DB / ANY pointer", desc: "Full pointer for DB data, parameters and ANY types (passing arrays / structures to blocks).", ex: "L   P#DB10.DBX0.0" },
    ],
  },
  {
    group: "Indirect addressing",
    items: [
      { mn: "[MDx]", name: "Memory-indirect", desc: "Effective address taken from a doubleword that holds a P# pointer.", ex: "A   M[MD4]" },
      { mn: "[AR1,P#]", name: "Register-indirect (area-internal)", desc: "Effective address = AR1 + the P# offset, within the operand's own area.", ex: "A   I[AR1,P#0.0]" },
      { mn: "[AR1,P#] ×area", name: "Register-indirect (area-crossing)", desc: "AR1 carries the area too, so a single pointer can address I / Q / M / DB. Common for DB access.", ex: "L   DBW[AR1,P#2.0]" },
    ],
  },
];

// Full S7 STL master reference — every instruction family, shown in the Help modal.
const STL_FULL_REF = [
  { group: "Bit logic (→ contacts)", items: [
    { mn: "A / AN", name: "AND / AND-NOT", desc: "Series contact — normally open / normally closed.", ex: "A I0.0   AN I0.1" },
    { mn: "O / ON", name: "OR / OR-NOT", desc: "Parallel branch — NO / NC contact.", ex: "O M5.0" },
    { mn: "X / XN", name: "XOR / XOR-NOT", desc: "Exclusive-OR the operand into the logic result.", ex: "X I0.2" },
    { mn: "A( … )", name: "Nested bracket", desc: "Group a sub-expression; the whole group acts as one contact. Also O(, AN(, ON(.", ex: "A( O I0.0 O I0.1 )" },
    { mn: "NOT", name: "Negate RLO", desc: "Invert the current logic result (VKE/RLO).", ex: "NOT" },
    { mn: "SET / CLR", name: "Force RLO", desc: "Set the logic result to 1 / 0 unconditionally.", ex: "SET" },
    { mn: "SAVE", name: "Save RLO", desc: "Copy RLO to the BR status bit.", ex: "SAVE" },
  ]},
  { group: "Outputs (→ coils)", items: [
    { mn: "=", name: "Assign", desc: "Write the logic result to the operand — output coil ─( )─.", ex: "= Q0.0" },
    { mn: "S", name: "Set (latch)", desc: "Latch operand to 1 while RLO is 1 — ─(S)─. VKE persists to following writes.", ex: "S M10.0" },
    { mn: "R", name: "Reset (unlatch)", desc: "Reset operand to 0 while RLO is 1 — ─(R)─.", ex: "R M10.0" },
    { mn: "FP / FN", name: "Rising / falling edge", desc: "One-scan pulse on 0→1 / 1→0 edge; operand stores the edge-memory bit. Drawn as ─┤P├─ / ─┤N├─.", ex: "A I0.0  FP M1.0  = Q0.5" },
  ]},
  { group: "Timers (→ timer boxes)", items: [
    { mn: "SD", name: "On-delay (S_ODT / TON)", desc: "Output true after preset elapses. Preset via L S5T#…", ex: "L S5T#5S  SD T1" },
    { mn: "SF", name: "Off-delay (S_OFFDT / TOF)", desc: "Output stays true for the preset after input drops.", ex: "L S5T#10S  SF T2" },
    { mn: "SS", name: "Retentive on-delay (S_ODTS)", desc: "Keeps elapsed time when input drops; reset with R T.", ex: "SS T3" },
    { mn: "SP", name: "Pulse (S_PULSE)", desc: "Output pulse of preset length while input holds.", ex: "SP T4" },
    { mn: "SE", name: "Extended pulse (S_PEXT)", desc: "Full-length pulse even if input drops early.", ex: "SE T5" },
    { mn: "FR", name: "Free / enable", desc: "Re-enable a timer or counter for restart on next edge.", ex: "FR T1" },
  ]},
  { group: "Counters (→ counter boxes)", items: [
    { mn: "CU / CD", name: "Count up / down", desc: "Increment / decrement on a rising edge of RLO.", ex: "CU C1   CD C1" },
    { mn: "S C / R C", name: "Preset / reset counter", desc: "S loads the preset (L C#n first); R clears to 0.", ex: "L C#10  S C1" },
    { mn: "L / LC C", name: "Read count", desc: "Load counter value binary (L) or BCD (LC) into ACCU 1.", ex: "L C1  T MW10" },
  ]},
  { group: "Load / Transfer (→ MOVE boxes)", items: [
    { mn: "L", name: "Load", desc: "Load value into ACCU 1 (previous ACCU 1 shifts to ACCU 2).", ex: "L MW10   L 25   L S5T#5S" },
    { mn: "T", name: "Transfer", desc: "Store ACCU 1 to the operand — drawn as a MOVE (or math) box.", ex: "T MW100" },
    { mn: "LC", name: "Load BCD", desc: "Load timer/counter value in BCD form.", ex: "LC T1" },
    { mn: "TAK / PUSH / POP / ENT / LEAVE", name: "Accumulator stack", desc: "Swap ACCU1↔ACCU2 / rotate the accumulator stack.", ex: "TAK" },
    { mn: "INC / DEC", name: "Increment / decrement", desc: "Add / subtract an 8-bit constant to ACCU 1 low byte.", ex: "INC 1" },
    { mn: "CAW / CAD", name: "Swap byte order", desc: "Reverse bytes in ACCU 1 word / doubleword.", ex: "CAW" },
  ]},
  { group: "Math & word logic (→ function boxes)", items: [
    { mn: "+I −I *I /I", name: "Integer math (16-bit)", desc: "ACCU2 op ACCU1 → ACCU1. Drawn as ADD_I / SUB_I / MUL_I / DIV_I box on transfer.", ex: "L MW0  L MW2  +I  T MW4" },
    { mn: "+D −D *D /D MOD", name: "Double-integer math (32-bit)", desc: "Same for DINT; MOD gives the division remainder.", ex: "L MD0  L MD4  +D  T MD8" },
    { mn: "+R −R *R /R", name: "Real (floating-point) math", desc: "32-bit IEEE-754 REAL arithmetic.", ex: "L MD10  L MD14  *R  T MD18" },
    { mn: "ABS SQR SQRT EXP LN SIN COS TAN …", name: "Float functions", desc: "Unary functions on ACCU 1 (REAL).", ex: "L MD20  SQRT  T MD24" },
    { mn: "AW OW XOW / AD OD XOD", name: "Word logic", desc: "Bitwise AND / OR / XOR on word (W) or doubleword (D).", ex: "L MW0  L W#16#00FF  AW  T MW2" },
    { mn: "NEGI NEGD NEGR / INVI INVD", name: "Negate / invert", desc: "Two's complement / one's complement of ACCU 1.", ex: "L MW0  NEGI  T MW2" },
    { mn: "SLW SRW SLD SRD SSI SSD RLD RRD", name: "Shift / rotate", desc: "Shift or rotate ACCU 1 by N bits (operand or ACCU 2).", ex: "L MW0  SLW 4  T MW2" },
    { mn: "BTI ITB BTD DTB DTR ITD RND TRUNC", name: "Conversions", desc: "BCD↔INT↔DINT↔REAL conversions and rounding.", ex: "L MW0  ITB  T MW2" },
  ]},
  { group: "Compare (→ compare contacts)", items: [
    { mn: "==I <>I >I <I >=I <=I", name: "Integer compare", desc: "Compare ACCU 2 with ACCU 1; result becomes the RLO — acts like a contact.", ex: "L MW0  L 100  >I  = Q0.0" },
    { mn: "==D <>D … / ==R <>R …", name: "DINT / REAL compare", desc: "Same comparisons for 32-bit integer and floating point.", ex: "L MD0  L MD4  >=R" },
  ]},
  { group: "Jumps & control (→ annotations)", items: [
    { mn: "LABEL:", name: "Jump label", desc: "A name ending in ':' marks a jump target line.", ex: "NEXT: L MW0" },
    { mn: "JU / JC / JCN", name: "Jump always / if RLO=1 / if RLO=0", desc: "Branch to a label. Not drawable as pure ladder — shown as a dashed annotation box.", ex: "JC NEXT" },
    { mn: "JCB JNB JBI JNBI JO JOS", name: "Status-bit jumps", desc: "Jump on BR / OV / OS status bits.", ex: "JO ERR" },
    { mn: "JZ JN JP JM JPZ JMZ JUO", name: "Result jumps", desc: "Jump on ACCU 1 compared to zero (=0, ≠0, >0, <0, ≥0, ≤0, invalid).", ex: "JZ ZERO" },
    { mn: "LOOP", name: "Loop", desc: "Decrement ACCU 1 and jump to the label while it is > 0.", ex: "L 10  T MW100 … LOOP LOOP1" },
    { mn: "MCR( )MCR MCRA MCRD", name: "Master Control Relay", desc: "Zone control — outputs inside an active MCR zone are forced off.", ex: "MCRA  MCR(  …  )MCR" },
  ]},
  { group: "Blocks & data blocks", items: [
    { mn: "CALL / CC / UC", name: "Call block", desc: "Call FB/FC/SFC — conditional (CC) or unconditional (UC/CALL). Drawn as a call box.", ex: "CALL FB10, DB10" },
    { mn: "OPN", name: "Open data block", desc: "Open a DB (DB register) or instance DB (DI register) — sets the context for DBX/DBW access.", ex: "OPN DB10" },
    { mn: "CDB", name: "Exchange DB registers", desc: "Swap the DB and DI registers.", ex: "CDB" },
    { mn: "BE / BEU / BEC", name: "Block end", desc: "End block — unconditional (BEU) or conditional on RLO (BEC).", ex: "BEC" },
  ]},
  ...POINTER_REF.map(g => ({ ...g, group: "Pointers — " + g.group })),
];

function HighlightedCode({ code, lineNet }) {
  const lines = code.split("\n");
  return lines.map((line, idx) => {
    const nn = lineNet ? lineNet[idx] : 0;
    // tint NETWORK / TITLE header lines in their network color (layout-safe: color only)
    if (nn > 0 && /^\s*(NETWORK|TITLE)\b/i.test(line)) {
      return <div key={idx} style={{ color: netColor(nn), fontWeight: 700 }}>{line || "​"}</div>;
    }
    const ci = line.indexOf("//");
    let codePart = line, commentPart = null;
    if (ci >= 0) { codePart = line.slice(0, ci); commentPart = line.slice(ci); }
    const pieces = codePart.split(/(\s+|\(|\)|,)/).filter(p => p !== "");
    return (
      <div key={idx}>
        {pieces.map((p, i) => {
          if (/^\s+$/.test(p) || p === "(" || p === ")" || p === ",") return <span key={i}>{p}</span>;
          const cls = classify(p);
          return <span key={i} className={cls}>{p}</span>;
        })}
        {commentPart && <span className="t-comment">{commentPart}</span>}
        {line === "" && <span>{"​"}</span>}
      </div>
    );
  });
}

/* ============================================================= *
 *  CROSS-REFERENCE
 * ============================================================= */
function buildCrossRef(networks) {
  const map = new Map();
  const typeOf = (op) => {
    const c = disp(op);
    if (/^I/i.test(c)) return "Input (I)";
    if (/^Q/i.test(c)) return "Output (Q)";
    if (/^M/i.test(c)) return "Memory (M)";
    if (/^T\d/i.test(c)) return "Timer (T)";
    if (/^C\d/i.test(c)) return "Counter (C)";
    if (/^DB/i.test(c)) return "Data (DB)";
    return "Symbol/Other";
  };
  const add = (op, usage, net) => {
    if (!op) return;
    const key = disp(op);
    if (!key) return;
    if (!map.has(key)) map.set(key, { operand: key, type: typeOf(op), reads: 0, writes: 0, nets: new Set() });
    const e = map.get(key);
    if (usage === "r") e.reads++; else e.writes++;
    e.nets.add(net);
  };
  const walk = (n, net) => {
    if (!n) return;
    if (n.type === "CONTACT") { if (n.operand && !["NOT","COMPARE"].includes(n.kind)) add(n.operand, "r", net); return; }
    (n.children || []).forEach(c => walk(c, net));
  };
  networks.forEach(net => net.rungs.forEach(r => {
    walk(r.logic, net.number);
    (r.outputs || []).forEach(o => {
      if (["COIL","SET","RESET","PEDGE","NEDGE"].includes(o.kind)) add(o.operand, "w", net.number);
      else if (o.kind === "TIMER" || o.kind === "COUNTER") add(o.operand, "w", net.number);
      else if (o.kind === "MOVE") { add(o.src, "r", net.number); add(o.dst, "w", net.number); }
    });
  }));
  return [...map.values()].sort((a,b) => a.type.localeCompare(b.type) || a.operand.localeCompare(b.operand));
}

/* ============================================================= *
 *  ICONS
 * ============================================================= */
const Ico = ({d, ...p}) => <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...p}><path d={d}/></svg>;
const I = {
  play: "M5 3l14 9-14 9V3z", trash: "M3 6h18M8 6V4h8v2M6 6l1 14h10l1-14",
  doc: "M14 2H6a2 2 0 00-2 2v16a2 2 0 002 2h12a2 2 0 002-2V8z M14 2v6h6",
  download: "M12 3v12m0 0l-4-4m4 4l4-4M4 21h16", sun:"M12 3v2m0 14v2M5 5l1.5 1.5M17.5 17.5L19 19M3 12h2m14 0h2M5 19l1.5-1.5M17.5 6.5L19 5M12 8a4 4 0 100 8 4 4 0 000-8z",
  moon:"M21 12.8A9 9 0 1111.2 3 7 7 0 0021 12.8z", img:"M3 5h18v14H3z M3 15l5-5 4 4 3-3 6 6", print:"M6 9V2h12v7M6 18H4a2 2 0 01-2-2v-5a2 2 0 012-2h16a2 2 0 012 2v5a2 2 0 01-2 2h-2M6 14h12v8H6z",
  zin:"M11 4a7 7 0 100 14 7 7 0 000-14zM21 21l-4.3-4.3M11 8v6M8 11h6", zout:"M11 4a7 7 0 100 14 7 7 0 000-14zM21 21l-4.3-4.3M8 11h6",
  fit:"M4 9V4h5M20 9V4h-5M4 15v5h5M20 15v5h-5",
  shrink:"M9 9H4M9 9V4M9 9L4 4M15 9h5M15 9V4M15 9l5-5M9 15H4M9 15v5M9 15l-5 5M15 15h5M15 15v5M15 15l5 5",
  reset:"M3 12a9 9 0 109-9 9 9 0 00-6.4 2.6L3 8M3 3v5h5",
  camera:"M23 19a2 2 0 01-2 2H3a2 2 0 01-2-2V8a2 2 0 012-2h4l2-3h6l2 3h4a2 2 0 012 2zM12 17a4 4 0 100-8 4 4 0 000 8z",
  globe:"M12 2a10 10 0 100 20 10 10 0 000-20M2 12h20M12 2a15 15 0 010 20M12 2a15 15 0 000 20",
  x:"M18 6L6 18M6 6l12 12", check:"M20 6L9 17l-5-5", upload:"M12 3v12M8 7l4-4 4 4M4 17v2a2 2 0 002 2h12a2 2 0 002-2v-2",
  shutter:"M12 2a10 10 0 100 20 10 10 0 000-20zM12 7a5 5 0 100 10 5 5 0 000-10z",
  help:"M12 2a10 10 0 100 20 10 10 0 000-20M9.1 9a3 3 0 015.8 1c0 2-3 3-3 3M12 17h.01"
};

/* ============================================================= *
 *  SCAN MODAL  (camera / image  ->  OCR  ->  STL)
 * ============================================================= */
function ScanModal({ onClose, onInsert }) {
  const [mode, setMode] = useState("choose"); // choose | camera | preview | done
  const [img, setImg] = useState(null);
  const [busy, setBusy] = useState(false);
  const [prog, setProg] = useState(0);
  const [status, setStatus] = useState("");
  const [text, setText] = useState("");
  const videoRef = useRef(null), fileRef = useRef(null), streamRef = useRef(null);

  const stopCam = () => { if (streamRef.current) { streamRef.current.getTracks().forEach(t => t.stop()); streamRef.current = null; } };
  useEffect(() => () => stopCam(), []);
  useEffect(() => {
    const onKey = (e) => { if (e.key === "Escape" && !busy) { stopCam(); onClose(); } };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [busy, onClose]);

  const startCam = async () => {
    setStatus("");
    try {
      const stream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: "environment" } });
      streamRef.current = stream;
      setMode("camera");
      setTimeout(() => { if (videoRef.current) { videoRef.current.srcObject = stream; videoRef.current.play().catch(() => {}); } }, 30);
    } catch (e) { setStatus("Camera unavailable — use “Upload image” instead. (" + (e.name || e) + ")"); }
  };

  const capture = () => {
    const v = videoRef.current; if (!v) return;
    const c = document.createElement("canvas");
    c.width = v.videoWidth || 1280; c.height = v.videoHeight || 720;
    c.getContext("2d").drawImage(v, 0, 0, c.width, c.height);
    setImg(c.toDataURL("image/png")); stopCam(); setMode("preview");
  };

  const onFile = (e) => {
    const f = e.target.files && e.target.files[0]; if (!f) return;
    const r = new FileReader(); r.onload = () => { setImg(r.result); setMode("preview"); }; r.readAsDataURL(f);
  };

  const runOCR = async () => {
    if (!img) return;
    setBusy(true); setProg(0); setStatus("Loading OCR engine…");
    try {
      const T = await loadTesseract();
      setStatus("Recognizing text…");
      const { data } = await T.recognize(img, "eng", { logger: m => { if (m.status === "recognizing text") setProg(Math.round(m.progress * 100)); } });
      const cleaned = cleanOcrStl(data.text);
      setText(cleaned); setMode("done");
      setStatus(cleaned.trim() ? "" : "No text detected — try a sharper, well-lit photo.");
    } catch (e) { setStatus("OCR failed: " + (e.message || e)); }
    setBusy(false);
  };

  const Big = ({ icon, label, sub, onClick }) => (
    <button onClick={onClick} className="flex-1 flex flex-col items-center gap-2 p-6 rounded-xl transition"
      style={{ background:"var(--panel2)", border:"1px solid var(--border)" }}
      onMouseOver={e=>e.currentTarget.style.borderColor="var(--accent)"} onMouseOut={e=>e.currentTarget.style.borderColor="var(--border)"}>
      <span style={{color:"var(--accent)"}}><Ico d={icon} width="30" height="30"/></span>
      <span className="font-semibold">{label}</span>
      <span className="text-xs text-center" style={{color:"var(--muted)"}}>{sub}</span>
    </button>
  );

  return (
    <div className="fixed inset-0 z-[80] flex items-center justify-center p-4" style={{ background:"rgba(0,0,0,.62)", backdropFilter:"blur(2px)" }} onClick={onClose}>
      <div className="w-full max-w-2xl rounded-2xl overflow-hidden flex flex-col anim-in" style={{ background:"var(--panel)", border:"1px solid var(--border)", maxHeight:"92vh" }} onClick={e => e.stopPropagation()}>
        <div className="flex items-center justify-between px-5 py-3" style={{ borderBottom:"1px solid var(--border)" }}>
          <div className="flex items-center gap-2 font-bold"><span style={{color:"var(--accent)"}}><Ico d={I.camera}/></span>Scan STL from Image</div>
          <button className="btn !px-2 !py-1" onClick={onClose}><Ico d={I.x}/></button>
        </div>
        <div className="p-5 overflow-auto">
          <input ref={fileRef} type="file" accept="image/*" capture="environment" className="hidden" onChange={onFile} />

          {mode === "choose" && (
            <div className="flex flex-col gap-4">
              <div className="flex gap-4">
                <Big icon={I.camera} label="Use Camera" sub="Take a photo of printed/handwritten STL" onClick={startCam} />
                <Big icon={I.upload} label="Upload Image" sub="Pick a photo or screenshot from your device" onClick={() => fileRef.current && fileRef.current.click()} />
              </div>
              <p className="text-xs" style={{color:"var(--muted)"}}>OCR runs locally via Tesseract.js (loaded from CDN on first use). Best results: sharp focus, good lighting, code roughly horizontal.</p>
            </div>
          )}

          {mode === "camera" && (
            <div className="flex flex-col items-center gap-3">
              <video ref={videoRef} playsInline muted className="w-full rounded-lg" style={{ maxHeight:"55vh", background:"#000" }} />
              <div className="flex gap-2">
                <button className="btn btn-primary" onClick={capture}><Ico d={I.shutter}/>Capture</button>
                <button className="btn" onClick={() => { stopCam(); setMode("choose"); }}>Cancel</button>
              </div>
            </div>
          )}

          {mode === "preview" && (
            <div className="flex flex-col items-center gap-3">
              <img src={img} alt="captured" className="w-full rounded-lg" style={{ maxHeight:"50vh", objectFit:"contain", background:"#000" }} />
              {busy && (
                <div className="w-full">
                  <div className="text-xs mb-1" style={{color:"var(--muted)"}}>{status} {prog>0 && prog+"%"}</div>
                  <div className="h-2 rounded-full overflow-hidden" style={{ background:"var(--panel2)" }}>
                    <div style={{ width:(prog||5)+"%", height:"100%", background:"var(--accent)", transition:".2s" }} />
                  </div>
                </div>
              )}
              <div className="flex gap-2">
                <button className="btn btn-primary" disabled={busy} onClick={runOCR}><Ico d={I.check}/>{busy ? "Working…" : "Extract STL"}</button>
                <button className="btn" disabled={busy} onClick={() => { setImg(null); setMode("choose"); }}>Retake</button>
              </div>
            </div>
          )}

          {mode === "done" && (
            <div className="flex flex-col gap-3">
              <div className="text-xs" style={{color:"var(--muted)"}}>Review &amp; fix the recognized text, then insert it. OCR isn't perfect — check operands and addresses.</div>
              <textarea className="mono w-full rounded-lg p-3" style={{ background:"var(--editorbg)", border:"1px solid var(--border)", color:"var(--text)", minHeight:"34vh", fontSize:"13px", lineHeight:"20px", whiteSpace:"pre", overflow:"auto" }}
                value={text} spellCheck={false} onChange={e => setText(e.target.value)} />
              {status && <div className="text-xs" style={{color:"var(--amber)"}}>{status}</div>}
              <div className="flex gap-2">
                <button className="btn btn-primary" disabled={!text.trim()} onClick={() => onInsert(text)}><Ico d={I.check}/>Insert &amp; Convert</button>
                <button className="btn" onClick={() => { setText(""); setImg(null); setMode("choose"); setStatus(""); }}>Scan again</button>
              </div>
            </div>
          )}

          {status && mode !== "preview" && mode !== "done" && <div className="text-xs mt-3" style={{color:"var(--amber)"}}>{status}</div>}
        </div>
      </div>
    </div>
  );
}

/* ============================================================= *
 *  POINTERS HELP MODAL  (STL pointers & indirect addressing)
 * ============================================================= */
function HelpModal({ onClose }) {
  const [q, setQ] = useState("");
  useEffect(() => {
    const onKey = (e) => { if (e.key === "Escape") onClose(); };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [onClose]);

  const ql = q.trim().toLowerCase();
  const match = (it) => !ql || it.mn.toLowerCase().includes(ql) || it.name.toLowerCase().includes(ql) || it.desc.toLowerCase().includes(ql);

  return (
    <div className="fixed inset-0 z-[80] flex items-center justify-center p-4" style={{ background: "rgba(0,0,0,.62)", backdropFilter: "blur(2px)" }} onClick={onClose}>
      <div className="w-full max-w-2xl rounded-2xl overflow-hidden flex flex-col anim-in" style={{ background: "var(--panel)", border: "1px solid var(--border)", maxHeight: "92vh" }} onClick={e => e.stopPropagation()}>
        <div className="flex items-center justify-between px-5 py-3" style={{ borderBottom: "1px solid var(--border)" }}>
          <div className="flex items-center gap-2 font-bold"><span style={{ color: "var(--accent)" }}><Ico d={I.help} /></span>STL Master Reference</div>
          <button className="btn !px-2 !py-1" onClick={onClose}><Ico d={I.x} /></button>
        </div>
        <div className="px-5 pt-3">
          <p className="text-xs mb-3" style={{ color: "var(--muted)" }}>
            The complete S7 STL instruction set and how each maps to ladder: bit logic → contacts, outputs → coils, timers/counters → boxes,
            math &amp; data moves → function boxes, jumps/pointers → annotations (they have no graphical LAD form — Siemens STEP 7 shows the same).
          </p>
          <input value={q} onChange={e => setQ(e.target.value)} placeholder="Search instructions… (e.g. LAR1, +I, OPN, LOOP)" className="mono w-full"
            style={{ padding: "9px 12px", borderRadius: 9, border: "1px solid var(--border)", background: "var(--editorbg)", color: "var(--text)", fontSize: 13, outline: "none", boxSizing: "border-box" }} />
        </div>
        <div className="px-5 py-3 overflow-auto">
          {STL_FULL_REF.map(grp => {
            const items = grp.items.filter(match);
            if (!items.length) return null;
            return (
              <div key={grp.group} className="mb-3">
                <div className="text-xs font-bold uppercase tracking-wider mb-1" style={{ color: "var(--accent)" }}>{grp.group}</div>
                {items.map(it => (
                  <div key={it.mn} className="flex items-start gap-3 py-2" style={{ borderBottom: "1px solid var(--border)" }}>
                    <span className="mono t-bool" style={{ fontWeight: 700, width: 110, flexShrink: 0, fontSize: 12.5, wordBreak: "break-word" }}>{it.mn}</span>
                    <div style={{ flex: 1 }}>
                      <div style={{ fontWeight: 600, fontSize: 13 }}>{it.name}</div>
                      <div style={{ fontSize: 12.5, color: "var(--muted)" }}>{it.desc}</div>
                    </div>
                    {it.ex && <span className="mono" style={{ fontSize: 11, color: "var(--operand)", maxWidth: 170, textAlign: "right", paddingTop: 2 }}>{it.ex}</span>}
                  </div>
                ))}
              </div>
            );
          })}
          <p className="text-xs mt-1" style={{ color: "var(--muted)" }}>
            Pointer format: a 32-bit pointer is <span className="mono">2#0000 aaa0 0000 0000 0000 0bbb bbbb bxxx</span> — area <span className="mono">aaa</span>, byte address <span className="mono">b…</span>, bit number <span className="mono">xxx</span>.
            Writing <span className="mono">P#10.0</span> means byte 10, bit 0.
          </p>
        </div>
      </div>
    </div>
  );
}

/* ============================================================= *
 *  AUTH GATE  (client-side password — deterrent, not server auth)
 *  Change the password locally with:  npm run set-password -- "yourPassword"
 * ============================================================= */
const PASSWORD_HASH = "e7c1a91471d9d97c4781a64e4c4cf4ee257019fa5a40f5bc1e4a71bc28ffb32f"; // default: stl2ladder
async function sha256Hex(str) {
  const buf = await crypto.subtle.digest("SHA-256", new TextEncoder().encode(str));
  return [...new Uint8Array(buf)].map(b => b.toString(16).padStart(2, "0")).join("");
}

function AuthGate({ children }) {
  const [authed, setAuthed] = useState(() => localStorage.getItem("stl_auth_ok") === PASSWORD_HASH);
  const [pw, setPw] = useState("");
  const [err, setErr] = useState(false);
  const [busy, setBusy] = useState(false);
  const inputRef = useRef(null);

  useEffect(() => { if (!authed && inputRef.current) inputRef.current.focus(); }, [authed]);

  if (authed) return children;

  const submit = async (e) => {
    e.preventDefault();
    setBusy(true); setErr(false);
    const ok = (await sha256Hex(pw)) === PASSWORD_HASH;
    setBusy(false);
    if (ok) { localStorage.setItem("stl_auth_ok", PASSWORD_HASH); setAuthed(true); }
    else { setErr(true); setPw(""); if (inputRef.current) inputRef.current.focus(); }
  };

  return (
    <div className="dark" style={{ position: "fixed", inset: 0, display: "flex", alignItems: "center", justifyContent: "center", background: "var(--bg)", padding: 16 }}>
      <form onSubmit={submit} className="anim-in" style={{ width: "100%", maxWidth: 360, background: "var(--panel)", border: "1px solid var(--border)", borderRadius: 18, padding: 28, textAlign: "center" }}>
        <div style={{ width: 52, height: 52, margin: "0 auto 14px", borderRadius: 14, display: "flex", alignItems: "center", justifyContent: "center", fontSize: 26, fontWeight: 700, background: "var(--accent)", color: "#04121a" }}>⎍</div>
        <div style={{ fontWeight: 700, fontSize: 18, color: "var(--text)" }}>STL → Ladder Converter</div>
        <div style={{ fontSize: 13, color: "var(--muted)", margin: "6px 0 20px" }}>This tool is private. Enter the password to continue.</div>
        <input
          ref={inputRef} type="password" value={pw} onChange={(e) => { setPw(e.target.value); setErr(false); }}
          placeholder="Password" autoComplete="current-password" className="mono"
          style={{ width: "100%", padding: "11px 14px", borderRadius: 10, border: `1px solid ${err ? "var(--coral)" : "var(--border)"}`, background: "var(--editorbg)", color: "var(--text)", fontSize: 14, outline: "none", boxSizing: "border-box" }}
        />
        {err && <div style={{ color: "var(--coral)", fontSize: 12, marginTop: 8 }}>Incorrect password. Try again.</div>}
        <button type="submit" disabled={busy || !pw} className="btn btn-primary" style={{ width: "100%", marginTop: 16, justifyContent: "center", opacity: (busy || !pw) ? 0.6 : 1 }}>
          {busy ? "Checking…" : "Unlock"}
        </button>
      </form>
    </div>
  );
}

/* ============================================================= *
 *  MAIN APP
 * ============================================================= */
function App() {
  const [dark, setDark] = useState(true);
  const [code, setCode] = useState(() => localStorage.getItem("stl_code") || EXAMPLES.motor.code);
  const [debounced, setDebounced] = useState(code);
  const [tab, setTab] = useState("ladder");
  const [zoom, setZoom] = useState(1);
  const [fs, setFs] = useState(false);
  const [translateOn, setTranslateOn] = useState(false);
  const [translations, setTranslations] = useState(() => { try { return JSON.parse(localStorage.getItem("stl_xlate") || "{}"); } catch (e) { return {}; } });
  const [trStatus, setTrStatus] = useState("");
  const [scanOpen, setScanOpen] = useState(false);
  const [helpOpen, setHelpOpen] = useState(false);
  const taRef = useRef(null), hlRef = useRef(null), gutterRef = useRef(null), scrollRef = useRef(null);
  const svgWrapRef = useRef(null);

  useEffect(() => { localStorage.setItem("stl_code", code); }, [code]);
  useEffect(() => { const t = setTimeout(() => setDebounced(code), 300); return () => clearTimeout(t); }, [code]);

  const parsed = useMemo(() => parseProgram(debounced), [debounced]);
  const networks = parsed.networks;
  const allWarnings = useMemo(() => networks.flatMap(n => n.warnings.map(w => ({ net: n.number, msg: w }))), [networks]);
  const errorCount = allWarnings.filter(w => /unbalanced|unrecognized/i.test(w.msg)).length;
  const warnCount = allWarnings.length - errorCount;
  const rungCount = networks.reduce((s, n) => s + n.rungs.length, 0);
  const crossRef = useMemo(() => buildCrossRef(networks), [networks]);

  // collect every unique comment used in the program
  const allComments = useMemo(() => {
    const set = new Set();
    const walk = (n) => { if (!n) return; if (n.type === "CONTACT") { if (n.comment) set.add(n.comment.trim()); return; } (n.children || []).forEach(walk); };
    networks.forEach(net => net.rungs.forEach(r => { walk(r.logic); (r.outputs || []).forEach(o => { if (o.comment) set.add(o.comment.trim()); }); }));
    return [...set].filter(Boolean);
  }, [networks]);

  // translate non-English comments -> English when the toggle is on
  useEffect(() => {
    if (!translateOn) { setTrStatus(""); return; }
    // when ON, translate every worded comment (API auto-detects; already-English ones come back ~unchanged)
    const hasWords = (c) => /[A-Za-z]{2,}/.test(c) || /[^\x00-\x7F]/.test(c);
    const pending = allComments.filter(c => hasWords(c) && !(c in translations));
    if (pending.length === 0) { setTrStatus(""); return; }
    let cancelled = false;
    (async () => {
      setTrStatus(`Translating ${pending.length}…`);
      const next = {};
      let failed = 0;
      for (const c of pending) {
        if (cancelled) return;
        const en = await translateOne(c);
        if (en && en !== c) next[c] = en; else if (en === null) failed++;
      }
      if (cancelled) return;
      setTranslations(prev => {
        const merged = { ...prev, ...next };
        try { localStorage.setItem("stl_xlate", JSON.stringify(merged)); } catch (e) {}
        return merged;
      });
      setTrStatus(failed ? `⚠ ${failed} couldn't be translated (offline?)` : "✓ Translated to English");
      setTimeout(() => !cancelled && setTrStatus(""), 2500);
    })();
    return () => { cancelled = true; };
  }, [translateOn, allComments]);

  const syncScroll = useCallback(() => {
    if (hlRef.current && taRef.current) {
      hlRef.current.scrollTop = taRef.current.scrollTop;
      hlRef.current.scrollLeft = taRef.current.scrollLeft;
    }
  }, []);

  const onScroll = (e) => {
    if (hlRef.current) { hlRef.current.scrollTop = e.target.scrollTop; hlRef.current.scrollLeft = e.target.scrollLeft; }
    if (gutterRef.current) gutterRef.current.scrollTop = e.target.scrollTop;
  };

  const handleTab = (e) => {
    if (e.key === "Tab") {
      e.preventDefault();
      const el = e.target, s = el.selectionStart, en = el.selectionEnd;
      const nv = code.slice(0, s) + "      " + code.slice(en);
      setCode(nv);
      requestAnimationFrame(() => { el.selectionStart = el.selectionEnd = s + 6; });
    }
  };

  const exportSVG = () => {
    const svg = document.getElementById("ladderSvg");
    if (!svg) return;
    const cs = getComputedStyle(document.body);
    const clone = svg.cloneNode(true);
    // inline computed colors so file is standalone
    inlineStyles(clone, cs);
    const data = new XMLSerializer().serializeToString(clone);
    const blob = new Blob(['<?xml version="1.0"?>\n' + data], { type: "image/svg+xml" });
    triggerDownload(URL.createObjectURL(blob), "ladder.svg");
  };

  const exportPNG = () => {
    const svg = document.getElementById("ladderSvg");
    if (!svg) return;
    const cs = getComputedStyle(document.body);
    const clone = svg.cloneNode(true);
    inlineStyles(clone, cs);
    const w = +svg.getAttribute("width"), h = +svg.getAttribute("height");
    const data = new XMLSerializer().serializeToString(clone);
    const img = new Image();
    const svgBlob = new Blob([data], { type: "image/svg+xml;charset=utf-8" });
    const url = URL.createObjectURL(svgBlob);
    img.onload = () => {
      const sc = 2, c = document.createElement("canvas");
      c.width = w*sc; c.height = h*sc;
      const ctx = c.getContext("2d");
      ctx.fillStyle = cs.getPropertyValue("--panel"); ctx.fillRect(0,0,c.width,c.height);
      ctx.scale(sc, sc); ctx.drawImage(img, 0, 0);
      URL.revokeObjectURL(url);
      triggerDownload(c.toDataURL("image/png"), "ladder.png");
    };
    img.src = url;
  };

  useEffect(() => {
    const onKey = (e) => {
      if ((e.ctrlKey||e.metaKey) && e.key.toLowerCase() === "s") { e.preventDefault(); exportSVG(); }
      else if ((e.ctrlKey||e.metaKey) && (e.key === "=" || e.key === "+")) { e.preventDefault(); setZoom(z=>Math.min(3, +(z+.15).toFixed(2))); }
      else if ((e.ctrlKey||e.metaKey) && e.key === "-") { e.preventDefault(); setZoom(z=>Math.max(.4, +(z-.15).toFixed(2))); }
      else if (e.key === "Escape") { setFs(false); }
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [code]);

  const lineCount = code.split("\n").length;
  const codeLines = useMemo(() => code.split("\n"), [code]);
  const lineNet = useMemo(() => lineNetworkMap(code), [code]);

  return (
    <div className={(dark ? "" : "light") + " flex flex-col h-screen"} style={{ background:"var(--bg)" }}>
      {/* TOOLBAR */}
      <header className="no-print flex items-center gap-2 px-4 py-2.5 flex-wrap" style={{ background:"var(--panel)", borderBottom:"1px solid var(--border)" }}>
        <div className="flex items-center gap-2 mr-2">
          <div className="w-8 h-8 rounded-lg flex items-center justify-center font-bold" style={{ background:"var(--accent)", color:"#04121a" }}>⎍</div>
          <div>
            <div className="font-bold text-sm leading-tight">STL → Ladder Converter</div>
            <div className="text-[11px] leading-tight" style={{color:"var(--muted)"}}>Siemens S7 · IEC 61131-3</div>
          </div>
        </div>
        <button className="btn btn-primary" onClick={() => setDebounced(code)}><Ico d={I.play}/>Convert</button>
        <button className="btn" onClick={() => setScanOpen(true)}><Ico d={I.camera}/>Scan</button>
        <button className="btn" title="Full STL instruction reference (incl. pointers & indirect addressing)" onClick={() => setHelpOpen(true)}><Ico d={I.help}/>STL Help</button>
        <button className="btn" onClick={() => setCode("")}><Ico d={I.trash}/>Clear</button>
        <select value="" onChange={(e) => { if (e.target.value) setCode(EXAMPLES[e.target.value].code); }}>
          <option value="">📂 Load Example…</option>
          {Object.entries(EXAMPLES).map(([k,v]) => <option key={k} value={k}>{v.name}</option>)}
        </select>
        <div className="flex-1" />
        {trStatus && <span className="text-xs mono" style={{color:"var(--muted)"}}>{trStatus}</span>}
        <button className={"btn "+(translateOn?"!border-[var(--accent)] !text-[var(--accent)]":"")} title="Auto-translate non-English comments to English" onClick={() => setTranslateOn(v => !v)}>
          <Ico d={I.globe}/>{translateOn ? "EN ✓" : "Translate"}
        </button>
        <button className="btn" onClick={exportSVG}><Ico d={I.download}/>SVG</button>
        <button className="btn" onClick={exportPNG}><Ico d={I.img}/>PNG</button>
        <button className="btn" onClick={() => window.print()}><Ico d={I.print}/>Print</button>
        <button className="btn" onClick={() => setDark(d => !d)}>
          <Ico d={dark ? I.sun : I.moon}/>{dark ? "Light" : "Dark"}
        </button>
      </header>

      {/* BODY */}
      <div className="flex-1 flex flex-col lg:flex-row min-h-0">
        {/* LEFT: EDITOR */}
        <section className="no-print flex flex-col lg:w-1/2 min-h-0 lg:border-r" style={{ borderColor:"var(--border)", height:"100%" }}>
          <div className="px-4 py-2 flex items-center justify-between" style={{ background:"var(--panel)", borderBottom:"1px solid var(--border)" }}>
            <span className="text-xs font-semibold uppercase tracking-wider" style={{color:"var(--muted)"}}>STL Source</span>
            <span className="text-xs mono" style={{color:"var(--muted)"}}>{lineCount} lines</span>
          </div>
          <div className="editor-wrap mono">
            <div className="editor-inner">
              <div className="gutter mono" ref={gutterRef} style={{overflow:"hidden"}}>
                {Array.from({length: lineCount}, (_,i) => {
                  const nn = lineNet[i] || 0;
                  const col = nn > 0 ? netColor(nn) : "transparent";
                  const isHdr = /^\s*NETWORK\b/i.test(codeLines[i] || "");
                  return <div key={i} style={{ borderLeft: `3px solid ${col}`, paddingLeft: 6, color: (isHdr && nn>0) ? col : undefined, fontWeight: isHdr ? 700 : undefined }}>{i+1}</div>;
                })}
              </div>
              <div className="code-area">
                <pre className="hl mono" ref={hlRef}><HighlightedCode code={code} lineNet={lineNet} /></pre>
                <textarea
                  ref={taRef} className="ta mono" value={code} spellCheck={false}
                  onChange={(e) => setCode(e.target.value)} onScroll={onScroll} onKeyDown={handleTab}
                  wrap="off"
                />
              </div>
            </div>
          </div>
        </section>

        {/* RIGHT: OUTPUT */}
        <section className={"flex flex-col min-h-0 print-full " + (fs ? "fixed inset-0 z-50" : "lg:w-1/2")}
                 style={{ height:"100%", background:"var(--panel)" }}>
          <div className="no-print flex items-center px-2" style={{ background:"var(--panel)", borderBottom:"1px solid var(--border)" }}>
            <div className={"tab "+(tab==="ladder"?"active":"")} onClick={()=>setTab("ladder")}>Ladder</div>
            <div className={"tab "+(tab==="xref"?"active":"")} onClick={()=>setTab("xref")}>Cross-Ref ({crossRef.length})</div>
            <div className={"tab "+(tab==="errors"?"active":"")} onClick={()=>setTab("errors")}>
              Messages {allWarnings.length>0 && <span style={{color:errorCount?"var(--coral)":"var(--amber)"}}>({allWarnings.length})</span>}
            </div>
            <div className="flex-1" />
            {tab==="ladder" && (
              <div className="flex items-center gap-1 pr-2">
                <button className="btn !px-2 !py-1" title="Zoom out" onClick={()=>setZoom(z=>Math.max(.4, +(z-.15).toFixed(2)))}><Ico d={I.zout}/></button>
                <button className="btn !px-2 !py-1 !min-w-[52px]" title="Reset zoom (100%)" onClick={()=>setZoom(1)}>
                  <span className="mono text-xs">{Math.round(zoom*100)}%</span>
                </button>
                <button className="btn !px-2 !py-1" title="Zoom in" onClick={()=>setZoom(z=>Math.min(3, +(z+.15).toFixed(2)))}><Ico d={I.zin}/></button>
                <button className={"btn !px-2 !py-1 "+(fs?"!border-[var(--accent)] !text-[var(--accent)]":"")} title={fs?"Exit full screen (Esc)":"Full screen"} onClick={()=>setFs(f=>!f)}>
                  <Ico d={fs ? I.shrink : I.fit}/>
                </button>
              </div>
            )}
          </div>

          <div className="flex-1 overflow-auto" style={{ background:"var(--panel2)" }} ref={svgWrapRef}>
            {tab==="ladder" && (
              networks.length === 0
                ? <Empty msg="No networks parsed. Load an example or type STL code." />
                : <div className="anim-in" style={{ padding:"8px 12px", width:"max-content" }}>
                    <Ladder networks={networks} themeKey={dark} zoom={zoom} xlate={translateOn ? translations : null} />
                  </div>
            )}
            {tab==="xref" && <CrossRefTable rows={crossRef} />}
            {tab==="errors" && <Messages items={allWarnings} onJump={()=>setTab("ladder")} />}
          </div>
        </section>
      </div>

      {/* STATUS BAR */}
      <footer className="no-print flex items-center gap-5 px-4 py-1.5 text-xs mono" style={{ background:"var(--panel)", borderTop:"1px solid var(--border)", color:"var(--muted)" }}>
        <span>● <b style={{color:"var(--accent)"}}>{networks.length}</b> networks</span>
        <span><b style={{color:"var(--green)"}}>{rungCount}</b> rungs</span>
        <span style={{color: warnCount?"var(--amber)":"inherit"}}>⚠ <b>{warnCount}</b> warnings</span>
        <span style={{color: errorCount?"var(--coral)":"inherit"}}>✕ <b>{errorCount}</b> errors</span>
        <div className="flex-1" />
        <span>{parsed.blockType ? `${parsed.blockType} ${disp(parsed.blockName)}` : "no block header"}</span>
        <span>Ready</span>
      </footer>

      {scanOpen && <ScanModal onClose={() => setScanOpen(false)} onInsert={(txt) => { setCode(txt); setDebounced(txt); setScanOpen(false); setTab("ladder"); }} />}
      {helpOpen && <HelpModal onClose={() => setHelpOpen(false)} />}
    </div>
  );
}

function Empty({ msg }) {
  return <div className="h-full flex items-center justify-center text-center px-8" style={{color:"var(--muted)"}}>
    <div><div className="text-4xl mb-3 opacity-50">⎍</div><div className="text-sm">{msg}</div></div>
  </div>;
}

function CrossRefTable({ rows }) {
  if (rows.length === 0) return <Empty msg="No operands found." />;
  return (
    <div className="p-3">
      <table className="w-full text-sm" style={{ borderCollapse:"collapse" }}>
        <thead>
          <tr style={{ color:"var(--muted)", textAlign:"left", borderBottom:"1px solid var(--border)" }}>
            <th className="py-2 px-2 font-semibold">Operand</th>
            <th className="py-2 px-2 font-semibold">Type</th>
            <th className="py-2 px-2 font-semibold text-center">Reads</th>
            <th className="py-2 px-2 font-semibold text-center">Writes</th>
            <th className="py-2 px-2 font-semibold">Networks</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((r,i) => (
            <tr key={i} style={{ borderBottom:"1px solid var(--border)" }}>
              <td className="py-1.5 px-2 mono font-semibold" style={{color:"var(--operand)"}}>{r.operand}</td>
              <td className="py-1.5 px-2" style={{color:"var(--muted)"}}>{r.type}</td>
              <td className="py-1.5 px-2 text-center mono">{r.reads||"–"}</td>
              <td className="py-1.5 px-2 text-center mono" style={{color: r.writes?"var(--amber)":"inherit"}}>{r.writes||"–"}</td>
              <td className="py-1.5 px-2 mono text-xs" style={{color:"var(--muted)"}}>{[...r.nets].join(", ")}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}

function Messages({ items, onJump }) {
  if (items.length === 0) return <div className="h-full flex items-center justify-center" style={{color:"var(--green)"}}>
    <div className="text-center"><div className="text-3xl mb-2">✓</div><div className="text-sm">No warnings or errors — clean conversion.</div></div>
  </div>;
  return (
    <div className="p-3 space-y-2">
      {items.map((it,i) => {
        const err = /unbalanced|unrecognized/i.test(it.msg);
        return (
          <div key={i} onClick={onJump} className="flex items-start gap-2 p-2.5 rounded-lg cursor-pointer text-sm"
            style={{ background:"var(--panel)", border:`1px solid ${err?"var(--coral)":"var(--amber)"}`, opacity:.95 }}>
            <span style={{color: err?"var(--coral)":"var(--amber)"}}>{err?"✕":"⚠"}</span>
            <div>
              <span className="mono text-xs px-1.5 py-0.5 rounded mr-2" style={{background:"var(--panel2)",color:"var(--accent)"}}>NW {it.net}</span>
              <span>{it.msg}</span>
            </div>
          </div>
        );
      })}
    </div>
  );
}

/* helpers for export */
function inlineStyles(clone, cs) {
  const vars = ["--wire","--accent","--green","--amber","--rail","--operand","--muted","--text","--boxfill","--border","--purple","--coral"];
  const resolve = {};
  vars.forEach(v => resolve[v] = cs.getPropertyValue(v).trim());
  const all = clone.querySelectorAll("*");
  const apply = (el) => {
    const cl = el.getAttribute("class") || "";
    const map = {
      wire:{stroke:resolve["--wire"],"stroke-width":2,fill:"none"},
      contact:{stroke:resolve["--accent"],"stroke-width":2.5,fill:"none"},
      coil:{stroke:resolve["--green"],"stroke-width":2.5,fill:"none"},
      "coil-sr":{stroke:resolve["--amber"],"stroke-width":2.5,fill:"none"},
      rail:{stroke:resolve["--rail"],"stroke-width":3},
      operand:{fill:resolve["--operand"],"font-family":"monospace","font-size":"12px","font-weight":600},
      symtext:{fill:resolve["--accent"],"font-weight":700,"font-size":"13px"},
      coiltext:{fill:resolve["--green"],"font-weight":700,"font-size":"13px"},
      "coiltext-sr":{fill:resolve["--amber"],"font-weight":700,"font-size":"13px"},
      boxrect:{fill:resolve["--boxfill"],stroke:resolve["--amber"],"stroke-width":2},
      boxtitle:{fill:resolve["--amber"],"font-size":"11px","font-weight":700},
      boxtext:{fill:resolve["--text"],"font-size":"11px"},
      nethdr:{fill:resolve["--accent"],"font-size":"13px","font-weight":700},
      netsub:{fill:resolve["--muted"],"font-size":"12px"},
      opcomment:{fill:resolve["--muted"],"font-size":"9.5px","font-style":"italic"},
      "addr-i":{fill:resolve["--accent"],"font-size":"10px","font-weight":700},
      "addr-q":{fill:resolve["--green"],"font-size":"10px","font-weight":700},
      "addr-tc":{fill:resolve["--amber"],"font-size":"10px","font-weight":700},
      "addr-m":{fill:resolve["--purple"],"font-size":"10px","font-weight":700},
      "iolab-i":{fill:resolve["--accent"],"font-size":"11px","font-weight":600},
      "iolab-q":{fill:resolve["--green"],"font-size":"11px","font-weight":600},
      jumpbox:{fill:"none",stroke:resolve["--amber"],"stroke-dasharray":"5 4","stroke-width":2},
      netsep:{stroke:resolve["--border"],"stroke-width":1,"stroke-dasharray":"3 4"},
    };
    cl.split(/\s+/).forEach(c => {
      if (map[c]) { const st = el.getAttribute("style")||""; const add = Object.entries(map[c]).map(([k,v])=>`${k}:${v}`).join(";"); el.setAttribute("style", st+";"+add); }
    });
  };
  all.forEach(apply);
}
function triggerDownload(url, name) {
  const a = document.createElement("a"); a.href = url; a.download = name; a.click();
}

createRoot(document.getElementById("root")).render(<AuthGate><App /></AuthGate>);
