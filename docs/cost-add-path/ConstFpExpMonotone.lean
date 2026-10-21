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


open Flapjack.Compiler.Backend.WordSimp
def xc (e : WordLangExpHOL (BitVec 64)) : Nat :=
  (lineBound preAllocLeafBudget (WordInst.instSelectExecutable riscvConfig 100000 (.assign 7 e))).getD 100000
def xs (e : WordLangExpHOL (BitVec 64)) : Nat :=
  (lineBound preAllocLeafBudget (WordInst.instSelectExecutable riscvConfig 100000 (.store e 7))).getD 100000

/-- (checked, violations) over the expressions constFpLoop rewrites -/
partial def chk (p : WordLangProgHOL (BitVec 64)) (cs : Spt (BitVec 64)) (acc : Nat × Nat × Int) : Nat × Nat × Int :=
  let one (e : WordLangExpHOL (BitVec 64)) (a : Nat × Nat × Int) : Nat × Nat × Int :=
    let d : Int := max ((xc (constFpExp e cs) : Int) - (xc e : Int)) ((xs (constFpExp e cs) : Int) - (xs e : Int))
    (a.1 + 1, if d > 0 then a.2.1 + 1 else a.2.1, max a.2.2 d)
  match p with
  | .seq a b => chk b (constFpLoop a cs).2 (chk a cs acc)
  | .ite cmp l r a b =>
      match sptLookup l cs, getVarImmCs r cs with
      | some x, some y => if Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y then chk a cs acc else chk b cs acc
      | _, _ => chk b cs (chk a cs acc)
  | .mustTerminate q => chk q cs acc
  | .loop _ b _ => chk b .ln acc
  | .call (some (n, names, k, _, _)) _ _ none =>
      chk k (deleteAll n (sptFilterV isGcConst (sptInter cs (allNames names)))) acc
  | .assign _ e | .store e _ | .shareInst _ _ e => one e acc
  | _ => acc

#eval do
  let mut a : Nat × Nat × Int := (0, 0, 0)
  for (x : Nat × Nat × WordLangProgHOL (BitVec 64)) in InitECandidate.Proofs.FrontendStages.Word.outputs do
    a := chk (WordSimp.seqAssoc .skip x.2.2) .ln a
  IO.println s!"expressions checked={a.1} violations={a.2.1} maxIncrease={a.2.2}"
