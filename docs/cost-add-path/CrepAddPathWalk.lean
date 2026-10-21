import InitECandidate.Proofs.FrontendStages.Crep.FunctionsFacts
open Flapjack

/-! Crep-level ADD path walk (diagnostic): the expressions and statements a
normal ADD iteration evaluates in the pinned Crep code, priced under the
default-Loop node costs (loopK), the selector node costs (selK) and the
source node costs (srcK = max), plus the CrepWorkS statement charges. -/

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
  loop : Nat := 0
  sel : Nat := 0
  src : Nat := 0
  stmt : Nat := 0
  dec : List Bool
  used : Nat := 0
  stop : Bool := false
  c : Cnt := {}
  calls : List String := []

def W.exp (w : W) (e : CrepExpHOL 64) : W :=
  { w with loop := w.loop + np loopK e, sel := w.sel + np selK e, src := w.src + np srcK e,
           c := cnt w.c e }

def W.exps (w : W) (es : List (CrepExpHOL 64)) : W := es.foldl W.exp w

/-- Consume the decisions of the comparisons an expression evaluates; return the last. -/
def W.decide (w : W) (n : Nat) : W × Bool :=
  let taken := w.dec.take n
  ({ w with dec := w.dec.drop n, used := w.used + n }, taken.getLastD false)

partial def walk (w : W) (p : CrepProgHOL 64) : W :=
  if w.stop then w else
  match p with
  | .seq a b => walk (walk w a) b
  | .skip | .tick => { w with stmt := w.stmt + (match p with | .tick => 37 | _ => 0) }
  | .dec _ e body =>
    let (w, _) := (w.exp e).decide (cmps e)
    walk w body
  | .assign _ e => ((w.exp e).decide (cmps e)).1
  | .storeGlob _ e | .shMem _ _ e => { ((w.exp e).decide (cmps e)).1 with stmt := w.stmt + 37 }
  | .store a v | .store32 a v | .storeByte a v =>
    { (((w.exp a).exp v).decide (cmps a + cmps v)).1 with stmt := w.stmt + 37 }
  | .ite c t e =>
    let w1 := { (w.exp c) with stmt := w.stmt + 37 }
    let (w2, b) := if cmps c = 0 then w1.decide 1 else w1.decide (cmps c)
    walk w2 (if b then t else e)
  | .while c body =>
    let w1 := { (w.exp c) with stmt := w.stmt + 111 }
    let (w2, b) := if cmps c = 0 then w1.decide 1 else w1.decide (cmps c)
    if b then { walk w2 body with stop := true } else w2
  | .call ret f args =>
    let w0 := w.exps args
    let fname : String := Flapjack.Basis.Pure.MlString.toStringOfBytes f
    let w1 : W := { w0 with stmt := w0.stmt + (196 + 40 * args.length) }
    let w1 : W := { w1 with calls := fname :: w1.calls }
    match ret with
    | none => { w1 with stop := true }
    | some _ => w1
  | .return vs => { (w.exps vs) with stmt := w.stmt + 37 + 40 * vs.length, stop := true }
  | .raise _ => { w with stmt := w.stmt + 86, stop := true }
  | .break _ | .continue _ => { w with stmt := w.stmt + 37, stop := true }
  | .extCall .. => { w with stmt := w.stmt + 37 }
  | .primitive ns _ as => { w with stmt := w.stmt + 85 + ns.length + as.length }

def decs : List (Nat × String × String × Nat) :=
  [(477, "stack_pop", "E", 2), (478, "stack_push", "EE", 1), (472, "charge_gas", "E", 1),
   (116, "u256_add", "", 1), (492, "pc_add", "", 1), (499, "op_add", "", 1),
   (597, "op_dispatch", "TTET", 1), (604, "run_frames", "TEEEE", 1)]

#eval do
  let outs := InitECandidate.Proofs.FrontendStages.Crep.outputs
  let mut tl := 0; let mut ts := 0; let mut tr := 0; let mut tst := 0
  let mut tc : Cnt := {}
  for (_, nm, (d : String), mult) in decs do
    match outs.find? (fun (o : _ × List Nat × CrepProgHOL 64) => Flapjack.Basis.Pure.MlString.toStringOfBytes o.1 == nm) with
    | some (_, _, body) =>
      let w := walk { dec := d.toList.map (· == 'T') } body
      IO.println s!"{nm} x{mult}: exprs loopK {w.loop} selK {w.sel} srcK {w.src} | stmts {w.stmt} | decisions used {w.used}/{d.length} | calls {w.calls.reverse}"
      tl := tl + mult * w.loop; ts := ts + mult * w.sel; tr := tr + mult * w.src; tst := tst + mult * w.stmt
      let c := w.c
      tc := { cst := tc.cst + mult * c.cst, var := tc.var + mult * c.var, top := tc.top + mult * c.top,
              load := tc.load + mult * c.load, ld32 := tc.ld32 + mult * c.ld32, op0 := tc.op0 + mult * c.op0,
              op1 := tc.op1 + mult * c.op1, op2 := tc.op2 + mult * c.op2, opMore := tc.opMore + mult * c.opMore,
              crepOp := tc.crepOp + mult * c.crepOp, shift := tc.shift + mult * c.shift, cmp := tc.cmp + mult * c.cmp }
    | none => IO.println s!"{nm}: missing"
  IO.println s!"TOTAL exprs loopK {tl} selK {ts} srcK {tr}; statements {tst}"
  IO.println s!"TOTAL CrepWork before (loopK) {tl + tst}  after (srcK) {tr + tst}  delta {tr - tl}"
  IO.println s!"nodes const {tc.cst} var {tc.var} top {tc.top} load {tc.load} ld32 {tc.ld32} op0 {tc.op0} op1 {tc.op1} op2 {tc.op2} op3+ {tc.opMore} crepOp {tc.crepOp} shift {tc.shift} cmp {tc.cmp}"
