import InitECandidate.Proofs.FrontendStages.Word.FunctionsFacts
import InitECandidate.Proofs.WordBackend.FunctionsFacts
import InitECandidate.Runtime.WordIselTransfer
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target InitECandidate.Runtime.FineCost

def selCost (e : WordLangExpHOL (BitVec 64)) : Nat :=
  InitECandidate.Runtime.FineCost.iselCost (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e))

def refined (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match InitECandidate.Runtime.WordToStack.refinedWordStackLeafBudget p with
  | some b => b
  | none => match p with
    | .ite _ _ _ _ _ => 23
    | .loop _ _ _ => 2
    | .call none _ _ _ => 41
    | .call (some (values,_,_,_,_)) _ args handler =>
        (if handler.isSome then 189 else 63)+39*(args.length+1-22)+21*(values.length+1-22)
    | _ => 0

def optP (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match p with
  | .move _ pairs => 24 * pairs.length
  | .inst _ | .get _ _ | .locValue _ _ | .opCurrHeap _ _ _ => max 24 (refined p)
  | _ => refined p

def preP (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match p with
  | .assign _ e => selCost e
  | .set _ e => selCost e + 12
  | .store e _ => selCost e + 24
  | .shareInst _ _ e => selCost e + 13
  | p => optP p

partial def sb : WordLangExpHOL (BitVec 64) → Nat
  | .const _ | .var _ | .lookup _ => 24
  | .load a => sb a + 24
  | .shift _ a b => sb a + sb b + 28
  | .op _ [] => 24
  | .op _ as => (as.map sb).sum + 24 * (as.length - 1)

def preB (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match p with
  | .assign _ e => sb e
  | .set _ e => sb e + 12
  | .store e _ => sb e + 24
  | .shareInst _ _ e => sb e + 13
  | p => optP p

def preX (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match p with
  | .assign _ _ | .set _ _ | .store _ _ | .shareInst _ _ _ =>
      (lineBound InitECandidate.Runtime.FineCost.preAllocLeafBudget (WordInst.instSelectExecutable riscvConfig 100000 p)).getD 100000
  | p => optP p

def tag : WordLangProgHOL (BitVec 64) → String
  | .move _ ps => s!"move {ps.length}"
  | .inst _ => "inst" | .assign _ (.const _) => "assignConst" | .assign _ _ => "assign"
  | .get _ _ => "get" | .set _ _ => "set" | .store _ _ => "store" | .tick => "tick"
  | .raise _ => "raise" | .return _ vs => s!"return {vs.length}" | .break _ => "break"
  | .continue _ => "continue" | .opCurrHeap _ _ _ => "opCurrHeap" | .locValue _ _ => "locValue"
  | .shareInst _ _ _ => "shareInst" | .skip => "skip" | _ => "OTHER"

partial def render (price : WordLangProgHOL (BitVec 64) → Nat) (ind : String) : WordLangProgHOL (BitVec 64) → List String
  | .seq a b => render price ind a ++ render price ind b
  | .skip => []
  | .mustTerminate b => render price ind b
  | p@(.ite _ _ _ t e) => [s!"{price p}\t{ind}IF"] ++ render price (ind ++ "  T ") t ++ render price (ind ++ "  E ") e
  | p@(.loop _ b _) => [s!"{price p}\t{ind}LOOP"] ++ render price (ind ++ "  ") b
  | p@(.call rets tgt args _) =>
      let nret := match rets with | some (r, _, _, _, _) => r.length | none => 0
      [s!"{price p}\t{ind}CALL f{tgt} args={args.length} rets={nret}"] ++
        (match rets with | some (_, _, k, _, _) => render price (ind ++ "  K ") k | none => [])
  | p => [s!"{price p}\t{ind}{tag p}"]


open Flapjack.Compiler.Backend.WordSimp

structure W where
  cost : Nat
  dec : List Bool
  used : Nat
  stop : Bool
  cs : Spt (BitVec 64)
  log : List String

/-- walk the executed path, resolving `ite`s constFp resolves (exact constFp constant sets);
others consume recorded decisions (true = T). -/
partial def walkP (price : WordLangProgHOL (BitVec 64) → Nat) (w : W) (p : WordLangProgHOL (BitVec 64)) : W :=
  if w.stop then w else
  match p with
  | .seq a b => walkP price (walkP price w a) b
  | .skip => w
  | .mustTerminate b => walkP price w b
  | .ite cmp lhs rhs t e =>
      let w := { w with cost := w.cost + price p }
      match sptLookup lhs w.cs, getVarImmCs rhs w.cs with
      | some clhs, some crhs =>
          let b := Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp clhs crhs
          walkP price { w with log := s!"static {b}" :: w.log } (if b then t else e)
      | _, _ =>
          let b := w.dec.headD false
          let w' := { w with dec := w.dec.tail, used := w.used + 1, log := s!"dyn {b}" :: w.log }
          walkP price w' (if b then t else e)
  | .loop _ body _ =>
      walkP price { w with cost := w.cost + price p, cs := .ln } body
  | .call ret _ _ handler =>
      let w := { w with cost := w.cost + price p }
      match ret, handler with
      | some (n, names, k, _, _), none =>
          let cs' := deleteAll n (sptFilterV isGcConst (sptInter w.cs (allNames names)))
          walkP price { w with cs := cs' } k
      | some (_, _, k, _, _), some _ => walkP price { w with cs := .ln } k
      | none, _ => { w with stop := true }
  | .return _ _ | .break _ | .continue _ => { w with cost := w.cost + price p, stop := true }
  | q => { w with cost := w.cost + price q, cs := (constFpLoop q w.cs).2 }

def decs : List (Nat × String × String) :=
  [(477, "stack_pop", "E"), (478, "stack_push", "EE"), (472, "charge_gas", "E"), (116, "u256_add", ""),
   (492, "pc_add", ""), (499, "op_add", ""), (597, "op_dispatch", "TTET"), (604, "run_frames", "TEEEE")]

#eval do
  let mut totX := 0; let mut totX1 := 0; let mut totB := 0; let mut totB1 := 0; let mut tot0 := 0; let mut tot1 := 0; let mut tot2 := 0; let mut tot3 := 0
  for (lab, argc', p) in InitECandidate.Proofs.FrontendStages.Word.outputs do
    match decs.find? (fun (x : Nat × String × String) => x.1 == lab) with
    | some (_, nm, d) =>
      let ds := d.toList.map (· == 'T')
      let w0 := walkP preP ⟨0, ds, 0, false, .ln, []⟩ (WordSimp.seqAssoc .skip p)
      let w2 := walkP optP ⟨0, ds, 0, false, .ln, []⟩ (WordInst.instSelectExecutable riscvConfig (maxVarHOL (WordSimp.compileExp p) + 1) (WordSimp.compileExp p))
      let w3 := walkP optP ⟨0, ds, 0, false, .ln, []⟩ (WordAlloc.fullSsaCcTrans argc' (WordInst.instSelectExecutable riscvConfig (maxVarHOL (WordSimp.compileExp p) + 1) (WordSimp.compileExp p)))
      let wB := walkP preB ⟨0, ds, 0, false, .ln, []⟩ (WordSimp.seqAssoc .skip p)
      let wB1 := walkP preB ⟨0, ds, 0, false, .ln, []⟩ (WordSimp.compileExp p)
      let multB := if lab == 477 then 2 else 1
      let wX := walkP preX ⟨0, ds, 0, false, .ln, []⟩ (WordSimp.seqAssoc .skip p)
      let wX1 := walkP preX ⟨0, ds, 0, false, .ln, []⟩ (WordSimp.compileExp p)
      totX := totX + multB * wX.cost; totX1 := totX1 + multB * wX1.cost
      totB := totB + multB * wB.cost; totB1 := totB1 + multB * wB1.cost
      let w1 := walkP preP ⟨0, ds, 0, false, .ln, []⟩ (WordSimp.compileExp p)
      let mult := if lab == 477 then 2 else 1
      tot0 := tot0 + mult * w0.cost; tot1 := tot1 + mult * w1.cost
      IO.println s!"  {nm} path0 {(w0.log.reverse)}"
      IO.println s!"{nm} x{mult}: pre-WordSimp {w0.cost} (dyn used {w0.used}/{d.length}, static {(w0.log.filter (fun (x : String) => x.startsWith "static")).length}) | WordSimp-out {w1.cost} (dyn {w1.used}) | isel@opt {w2.cost} (dyn {w2.used}) | SSA@opt {w3.cost} (dyn {w3.used})"
      tot2 := tot2 + mult * w2.cost; tot3 := tot3 + mult * w3.cost
    | none => pure ()
  IO.println s!"TOTAL pre-WordSimp@preB {totB}  WordSimp-out@preB {totB1}  pre-WordSimp@exactIsel {totX}  WordSimp-out@exactIsel {totX1}"
  let mut tot4 := 0; let mut totF := 0
  for (lab, argc', p) in InitECandidate.Proofs.FrontendStages.Word.outputs do
    match decs.find? (fun (x : Nat × String × String) => x.1 == lab) with
    | some (_, nm, d) =>
      let ds := d.toList.map (· == 'T')
      let p0 := WordSimp.compileExp p
      let p3 := WordAlloc.removeDeadProg (WordAlloc.fullSsaCcTrans argc' (WordInst.instSelectExecutable riscvConfig (maxVarHOL p0 + 1) p0))
      let w4 := walkP optP ⟨0, ds, 0, false, .ln, []⟩ p3
      let fin := (InitECandidate.Proofs.WordBackend.outputs.find? (fun (x : Nat × Nat × WordLangProgHOL (BitVec 64)) => x.1 == lab)).map (fun (x : Nat × Nat × WordLangProgHOL (BitVec 64)) => x.2.2)
      let wF := walkP optP ⟨0, ds, 0, false, .ln, []⟩ (fin.getD .skip)
      let mult := if lab == 477 then 2 else 1
      tot4 := tot4 + mult * w4.cost; totF := totF + mult * wF.cost
      IO.println s!"{nm}: removeDead@opt {w4.cost} (dyn {w4.used}) final@opt {wF.cost} (dyn {wF.used})"
    | none => pure ()
  IO.println s!"TOTAL removeDead@opt {tot4} final@opt {totF}"
  IO.println s!"TOTAL pre-WordSimp@preIsel {tot0}  WordSimp-out@preIsel {tot1}  isel@opt {tot2}  SSA@opt {tot3}"
