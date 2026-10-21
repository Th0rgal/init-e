import CandidateAst
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.PanStructs.CompileDeclsExact
import Flapjack.Pancake.PanGlobals.CompileTopExact
import Flapjack.Pancake.PanToCrep.CompileExact
import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.LoopToWord.CompFuncExact
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


open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def cds : List (Pancake.PanLang.DeclHOL 64) :=
  Candidate.guestAst.map Pancake.PanLang.declToHOL
def cp1 := Pancake.PanStructs.CompileShapeExact.compileTopExact cds
def cp2 := compileTopExactHOL cp1 (Basis.Pure.MlString.ofString "main")
def cp3 : List (Pancake.PanLang.MlS × List Nat × CrepProgHOL 64) := compileProgDeclsHOLW cp2
def cp4 : List (Nat × List Nat × HolLoopProg 64) :=
  compileProgHOLExact Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig.isa cp3
def cw : List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  (cp3.map (fun x => x.1)).zip cp4 |>.zipIdx |>.map fun ((nm, (idx, params, body)), i) =>
    (i + 64, params.length + 1, loopToWordCompFuncHOL (i + 64) params body)

partial def loopBody : WordLangProgHOL (BitVec 64) → Option (WordLangProgHOL (BitVec 64))
  | .seq a b => match loopBody a with | some x => some x | none => loopBody b
  | .loop _ body _ => some body
  | .mustTerminate b => loopBody b
  | _ => none

def target := [(103,"find_leaf"),(104,"find_leaf_path"),(109,"set"),(108,"grow"),(117,"copy"),(111,"truncate")]

unsafe def main : IO Unit := do
  for (lab,nm) in target do
    let some (_, argc, p) := cw.find? (fun x => x.1 == lab) | continue
    let p0 := WordSimp.seqAssoc .skip p
    let probes := ["TET","TEE","TETT","TETE","TE","TETET"]
    for probe in probes do
      let ds := probe.toList.map (· == 'T')
      let w := walkP preX ⟨0, ds, 0, false, .ln, []⟩ p0
      IO.println s!"{lab} {nm} {probe}: preX {w.cost} used {w.used} stop {w.stop}"
      match loopBody p0 with
      | some body =>
          let wb := walkP preX ⟨0, ds, 0, false, .ln, []⟩ body
          IO.println s!"  body {probe}: preX {wb.cost} used {wb.used} stop {wb.stop}"
      | none => pure ()
