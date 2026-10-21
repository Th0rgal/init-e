import InitECandidate.Proofs.FrontendStages.Crep.FunctionsFacts
import InitECandidate.Runtime.WordIselTransfer
import InitECandidate.Runtime.SourceSiteMoves
import InitECandidate.Runtime.SourceCostLoopWorkWs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target InitECandidate.Runtime.FineCost

/-! Crep-level ADD path walk (diagnostic): the expressions and statements a
normal ADD iteration evaluates in the pinned Crep code, priced under the
default-Loop node costs (loopK), the selector node costs (selK) and the
source node costs (srcK = max), plus the CrepWorkS statement charges. -/

partial def toLoop : CrepExpHOL 64 → Option (HolLoopExp 64)
  | .const w => some (.const w)
  | .var n => some (.var n)
  | .baseAddr => some .baseAddr
  | .topAddr => some .topAddr
  | .load a => (toLoop a).map .load
  | .op o as => (as.mapM toLoop).map (.op o)
  | .shift o a n => none
  | _ => none

def imm12 (w : BitVec 64) : Bool := w.toInt < 2048 && -2048 ≤ w.toInt

def isOp (o : BinOp) : CrepExpHOL 64 → Bool
  | .op o' _ => o == o'
  | _ => false

/-- Candidate pattern-aware structural price. -/
partial def nodeT : CrepExpHOL 64 → Nat
  | .const _ | .var _ | .loadGlob _ | .baseAddr => 24
  | .topAddr => 72
  | .load (.op .add [a, .const w]) =>
      if !(isOp .add a) && imm12 w then nodeT a + 24 else nodeT (.op .add [a, .const w]) + 24
  | .load (.op .sub [a, .const w]) =>
      if !(isOp .add a) && imm12 (-w) then nodeT a + 24 else nodeT (.op .sub [a, .const w]) + 24
  | .load a => nodeT a + 24
  | .load32 a | .loadByte a => nodeT a + 48
  | .op o [a, .const w] =>
      let same := isOp o a || (o == .sub && isOp .add a)
      if same then nodeT a + 24 + 48
      else if (o == .sub && imm12 (-w)) || (o != .sub && imm12 w) then nodeT a + 24 else nodeT a + 48
  | .op _ args => (args.map nodeT).sum + 24 * (args.length - 1) + 24 * (1 - args.length)
  | .crepOp _ args => (args.map nodeT).sum + 51
  | .shift _ l (.const n) => if n.toNat < 64 then nodeT l + 24 else 24
  | .shift _ l r => nodeT l + nodeT r + 28
  | .cmp _ l r => nodeT l + nodeT r + 85

def actualE (e : HolLoopExp 64) : Option Nat :=
  lineBound preAllocLeafBudget
    (WordInst.instSelectExecutable riscvConfig 100000 (.assign 7 (LoopToWord.compExpHOL .ln e)))

structure K where
  cst : Nat
  var : Nat
  top : Nat
  load : Nat
  ld32 : Nat
  op : Nat → Nat
  crepOp : Nat
  shift : Nat
  cmp : Nat

def loopK : K := ⟨19, 14, 81, 21, 49, fun n => 28 * (n - 1) + 19 * (1 - (n - 1)), 57, 32, 70⟩
def selK : K := ⟨24, 24, 124, 24, 48, fun n => 24 * (n - 1) + 24 * (1 - n), 51, 28, 85⟩
def srcK : K := ⟨24, 24, 124, 24, 49,
  fun n => max (28 * (n - 1) + 19 * (1 - (n - 1))) (24 * (n - 1) + 24 * (1 - n)), 57, 32, 85⟩

partial def np (k : K) : CrepExpHOL 64 → Nat
  | .const _ => k.cst
  | .var _ | .loadGlob _ | .baseAddr => k.var
  | .topAddr => k.top
  | .load a => np k a + k.load
  | .load32 a | .loadByte a => np k a + k.ld32
  | .op _ as => (as.map (np k)).sum + k.op as.length
  | .crepOp _ as => (as.map (np k)).sum + k.crepOp
  | .shift _ l r => np k l + np k r + k.shift
  | .cmp _ l r => np k l + np k r + k.cmp

/-- Crep nodes that become Loop variables (their code is priced separately). -/
def loopVar : CrepExpHOL 64 → Bool
  | .cmp .. | .crepOp .. | .load32 _ | .loadByte _ => true
  | _ => false

/-- Operands whose pulled form is not an `op o` (no merge) and not a constant. -/
def safeFor (o : BinOp) : CrepExpHOL 64 → Bool
  | .var _ | .loadGlob _ | .baseAddr | .load _ | .shift .. => true
  | .topAddr => o != .add
  | e => loopVar e

/-- Conservative provable pattern-aware price. -/
partial def nodeC : CrepExpHOL 64 → Nat
  | .const _ | .var _ | .loadGlob _ | .baseAddr => 24
  | .topAddr => 72
  | .load (.op .sub [a, .const w]) =>
      if !(a matches .const _) && imm12 (-w) then nodeC a + 24 else np selK (.load (.op .sub [a, .const w]))
  | .load (.op .add [a, .const w]) =>
      if safeFor .add a && imm12 w then nodeC a + 24 else nodeC (.op .add [a, .const w]) + 24
  | .load a => nodeC a + 24
  | .load32 a | .loadByte a => nodeC a + 48
  | .op .sub [a, .const w] =>
      if !(a matches .const _) then nodeC a + (if imm12 (-w) then 24 else 48) else np selK (.op .sub [a, .const w])
  | .op o [a, .const w] =>
      if safeFor o a then nodeC a + (if imm12 w then 24 else 48) else np selK (.op o [a, .const w])
  | .op .sub [a, b] =>
      if !(a matches .const _) && !(b matches .const _) then nodeC a + nodeC b + 24 else np selK (.op .sub [a, b])
  | .op o [a, b] => if safeFor o a && safeFor o b then nodeC a + nodeC b + 24 else np selK (.op o [a, b])
  | .crepOp _ args => (args.map nodeC).sum + 51
  | .shift _ l (.const n) => if n.toNat < 64 then nodeC l + 24 else 24
  | .shift _ l r => nodeC l + nodeC r + 28
  | .cmp _ l r => nodeC l + nodeC r + 85
  | e => np selK e

partial def cmps : CrepExpHOL 64 → Nat
  | .load a | .load32 a | .loadByte a => cmps a
  | .op _ as | .crepOp _ as => (as.map cmps).sum
  | .shift _ l r => cmps l + cmps r
  | .cmp _ l r => cmps l + cmps r + 1
  | _ => 0

/-- Per-node counts by kind, for the per-event delta. -/
structure Cnt where
  cst : Nat := 0
  var : Nat := 0
  top : Nat := 0
  load : Nat := 0
  ld32 : Nat := 0
  op0 : Nat := 0
  op1 : Nat := 0
  op2 : Nat := 0
  opMore : Nat := 0
  crepOp : Nat := 0
  shift : Nat := 0
  cmp : Nat := 0

partial def cnt (c : Cnt) : CrepExpHOL 64 → Cnt
  | .const _ => { c with cst := c.cst + 1 }
  | .var _ | .loadGlob _ | .baseAddr => { c with var := c.var + 1 }
  | .topAddr => { c with top := c.top + 1 }
  | .load a => cnt { c with load := c.load + 1 } a
  | .load32 a | .loadByte a => cnt { c with ld32 := c.ld32 + 1 } a
  | .op _ as =>
    let c := match as.length with
      | 0 => { c with op0 := c.op0 + 1 } | 1 => { c with op1 := c.op1 + 1 }
      | 2 => { c with op2 := c.op2 + 1 } | _ => { c with opMore := c.opMore + 1 }
    as.foldl cnt c
  | .crepOp _ as => as.foldl cnt { c with crepOp := c.crepOp + 1 }
  | .shift _ l r => cnt (cnt { c with shift := c.shift + 1 } l) r
  | .cmp _ l r => cnt (cnt { c with cmp := c.cmp + 1 } l) r

structure W where
  tops : List Int := []
  cons : Nat := 0
  mx : Nat := 0
  tgt : Nat := 0
  viol : Nat := 0
  act : Nat := 0
  loop : Nat := 0
  sel : Nat := 0
  src : Nat := 0
  stmt : Nat := 0
  dec : List Bool
  used : Nat := 0
  stop : Bool := false
  c : Cnt := {}
  calls : List String := []
  nstmt : Nat := 0
  cdet : List (String × Nat × Nat) := []
  bk : List (String × Nat × Nat) := []

partial def topOffs : CrepExpHOL 64 → List Int
  | .op .sub [.topAddr, .const w] => [w.toInt]
  | .load a | .load32 a | .loadByte a => topOffs a
  | .op _ as | .crepOp _ as => (as.map topOffs).flatten
  | .shift _ l r | .cmp _ l r => topOffs l ++ topOffs r
  | _ => []

def W.exp (w : W) (e : CrepExpHOL 64) : W :=
  let a := match toLoop e with
    | some le => (actualE le).getD (np selK e)
    | none => np selK e
  let t := nodeT e
  let bad := match toLoop e with
    | some le => match actualE le with | some x => decide (x > t) | none => false
    | none => false
  { w with tops := w.tops ++ topOffs e, cons := w.cons + nodeC e, mx := w.mx + max t (np loopK e), tgt := w.tgt + t, viol := w.viol + (if bad then 1 else 0), act := w.act + a, loop := w.loop + np loopK e, sel := w.sel + np selK e, src := w.src + np srcK e,
           c := cnt w.c e }

def W.exps (w : W) (es : List (CrepExpHOL 64)) : W := es.foldl W.exp w

/-- Consume the decisions of the comparisons an expression evaluates; return the last. -/
def W.decide (w : W) (n : Nat) : W × Bool :=
  let taken := w.dec.take n
  ({ w with dec := w.dec.drop n, used := w.used + n }, taken.getLastD false)

def W.b (w : W) (k : String) (u : Nat) : W :=
  let rec go : List (String × Nat × Nat) → List (String × Nat × Nat)
    | [] => [(k, 1, u)]
    | (k', n, v) :: r => if k' == k then (k', n + 1, v + u) :: r else (k', n, v) :: go r
  { w with bk := go w.bk }

partial def walk (w : W) (p : CrepProgHOL 64) : W :=
  if w.stop then w else
  match p with
  | .seq a b => walk (walk w a) b
  | .skip => w
  | .tick => ({ w with stmt := w.stmt + 37, nstmt := w.nstmt + 6 }).b "tick" 37
  | .dec _ e body =>
    let (w, _) := (w.exp e).decide (cmps e)
    walk w body
  | .assign _ e => ((w.exp e).decide (cmps e)).1
  | .storeGlob _ e | .shMem _ _ e => ({ ((w.exp e).decide (cmps e)).1 with stmt := w.stmt + 37, nstmt := w.nstmt + 13 }).b "storeGlob/shMem" 37
  | .store a v | .store32 a v | .storeByte a v =>
    ({ (((w.exp a).exp v).decide (cmps a + cmps v)).1 with stmt := w.stmt + 37, nstmt := w.nstmt + 24 }).b "store" 37
  | .ite c t e =>
    let w1 := ({ (w.exp c) with stmt := w.stmt + 37, nstmt := w.nstmt + 29 }).b "ite" 37
    let (w2, b) := if cmps c = 0 then w1.decide 1 else w1.decide (cmps c)
    walk w2 (if b then t else e)
  | .while c body =>
    let w1 := ({ (w.exp c) with stmt := w.stmt + 111, nstmt := w.nstmt + 45 }).b "while" 111
    let (w2, b) := if cmps c = 0 then w1.decide 1 else w1.decide (cmps c)
    if b then { walk w2 body with stop := true } else w2
  | .call ret f args =>
    let w0 := w.exps args
    let fname : String := Flapjack.Basis.Pure.MlString.toStringOfBytes f
    let w1 : W := ({ w0 with stmt := w0.stmt + (196 + 40 * args.length) }).b (s!"call args={args.length}") (196 + 40 * args.length)
    let rc := match ret with | some (rts, _) => rts.length | none => 0
    let w1 : W := { w1 with calls := fname :: w1.calls, cdet := w1.cdet ++ [(fname, args.length, rc)] }
    match ret with
    | none => { w1 with stop := true }
    | some _ => w1
  | .return vs => ({ (w.exps vs) with stmt := w.stmt + 37 + 40 * vs.length, nstmt := w.nstmt + 15, stop := true }).b (s!"return {vs.length}") (37 + 40 * vs.length)
  | .raise _ => ({ w with stmt := w.stmt + 86, nstmt := w.nstmt + 87, stop := true }).b "raise" 86
  | .break _ | .continue _ => ({ w with stmt := w.stmt + 37, nstmt := w.nstmt + 2, stop := true }).b "break/continue" 37
  | .extCall .. => ({ w with stmt := w.stmt + 37, nstmt := w.nstmt + 121 }).b "extCall" 37
  | .primitive ns _ as => ({ w with stmt := w.stmt + 85 + ns.length + as.length, nstmt := w.nstmt + 111 }).b "primitive" (85 + ns.length + as.length)

def decs : List (Nat × String × String × Nat) :=
  [(477, "stack_pop", "E", 2), (478, "stack_push", "EE", 1), (472, "charge_gas", "E", 1),
   (116, "u256_add", "", 1), (492, "pc_add", "", 1), (499, "op_add", "", 1),
   (597, "op_dispatch", "TTET", 1), (604, "run_frames", "TEEEE", 1)]

#eval do
  let outs := InitECandidate.Proofs.FrontendStages.Crep.outputs
  let mut tc2 := 0; let mut tm := 0; let mut tt := 0; let mut tv := 0; let mut ta := 0; let mut tl := 0; let mut ts := 0; let mut tr := 0; let mut tst := 0
  let mut tns := 0
  let mut tcall := 0
  let mut tsites := 0
  let mut tc : Cnt := {}
  let mut allb : List (String × Nat × Nat) := []
  for (lab, nm, (d : String), mult) in decs do
    match outs.find? (fun (o : _ × List Nat × CrepProgHOL 64) => Flapjack.Basis.Pure.MlString.toStringOfBytes o.1 == nm) with
    | some (n, _, body) =>
      let w := walk { dec := d.toList.map (· == 'T') } body
      IO.println s!"  {nm} topOffs {w.tops}"
      IO.println s!"{nm} x{mult}: exprs actual {w.act} loopK {w.loop} selK {w.sel} srcK {w.src} | stmts {w.stmt} | decisions used {w.used}/{d.length} | calls {w.calls.reverse}"
      ta := ta + mult * w.act; tt := tt + mult * w.tgt; tm := tm + mult * w.mx; tc2 := tc2 + mult * w.cons; tv := tv + w.viol; tl := tl + mult * w.loop; ts := ts + mult * w.sel; tr := tr + mult * w.src; tst := tst + mult * w.stmt; tns := tns + mult * w.nstmt
      for (g, a, rc) in w.cdet do
        let gm := Flapjack.Basis.Pure.MlString.ofString g
        let fm := Flapjack.Basis.Pure.MlString.ofString nm
        let cs := callSites fm gm
        let tsv := wsTail (functionLabel gm) + wsTail none
        let base := 195 + 39 * (a + 1 - 22) + 21 * (rc + 1 - 22)
        IO.println s!"  CALL {nm} -> {g} args {a} rets {rc} x{mult}: base {base} cs {cs} ts {tsv} | old 196+40a {196 + 40 * a} callMoves {callMoves fm gm}"
        tcall := tcall + mult * base; tsites := tsites + mult * (cs + tsv)
      for (k, n, u) in w.bk do
        allb := allb ++ [(k, mult * n, mult * u)]
      let c := w.c
      tc := { cst := tc.cst + mult * c.cst, var := tc.var + mult * c.var, top := tc.top + mult * c.top,
              load := tc.load + mult * c.load, ld32 := tc.ld32 + mult * c.ld32, op0 := tc.op0 + mult * c.op0,
              op1 := tc.op1 + mult * c.op1, op2 := tc.op2 + mult * c.op2, opMore := tc.opMore + mult * c.opMore,
              crepOp := tc.crepOp + mult * c.crepOp, shift := tc.shift + mult * c.shift, cmp := tc.cmp + mult * c.cmp }
    | none => IO.println s!"{nm}: missing"
  IO.println s!"TOTAL exprs nodeC {tc2} max(nodeT,loopK) {tm} nodeT {tt} (violations {tv}) actualSel {ta} loopK {tl} selK {ts} srcK {tr}; statements {tst}"
  IO.println s!"TOTAL CrepWork before (loopK) {tl + tst}  after (srcK) {tr + tst}  delta {tr - tl}"
  IO.println s!"MODEL stmts(non-call) {tns} calls base {tcall} call sites cs+ts {tsites}; model Crep work selK {ts + tns + tcall + tsites} nodeT {tt + tns + tcall + tsites} srcK {tr + tns + tcall + tsites}"
  let keys := (allb.map (fun (r : String × Nat × Nat) => r.1)).eraseDups
  for k in keys do
    let rows := allb.filter (fun (r : String × Nat × Nat) => r.1 == k)
    IO.println s!"STMT {k}: count {(rows.map (fun (r : String × Nat × Nat) => r.2.1)).sum} units {(rows.map (fun (r : String × Nat × Nat) => r.2.2)).sum}"
  IO.println s!"nodes const {tc.cst} var {tc.var} top {tc.top} load {tc.load} ld32 {tc.ld32} op0 {tc.op0} op1 {tc.op1} op2 {tc.op2} op3+ {tc.opMore} crepOp {tc.crepOp} shift {tc.shift} cmp {tc.cmp}"
