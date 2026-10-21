import InitECandidate.Runtime.SSAQuantitativeCost
import InitECandidate.Runtime.SSAReconciliationLineCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact

/-- A static entry allowance belongs to this invocation, separately from the
source executed cost. In particular, loop setup is not a repeated head fee. -/
def SSAQuantitativeAllowance {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (p : WordLangProgHOL (BitVec 64)) (source target : WordSemStateFiniteExact 64 C F)
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (entry : Nat) : Prop :=
  ∃ permutation,
    let compiled := ssaCcTrans p map next tables
    let sourceState := {source with permute := permutation}
    let sourceRun := evaluate p sourceState
    let targetRun := evaluate compiled.1 target
    sourceRun.1 = some .error ∨ sourceRun.1 = targetRun.1 ∧
      Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
      SSAResultLocals compiled.2.2 compiled.2.1 tables sourceRun.2.locals targetRun.2.locals sourceRun.1 ∧
      wordExecutionCost (fun q _ => TP q) compiled.1 target ≤
        wordExecutionCost (fun q _ => SP q) p sourceState + entry

/-- Smaller-body induction premise at one actual static compilation context.
State relations remain universally quantified; maps and loop tables do not. -/
def SSABodyAllowance {C F : Type} (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (body : WordLangProgHOL (BitVec 64)) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) (entry : Nat) : Prop :=
  ∀ (source target : WordSemStateFiniteExact 64 C F),
    Flapjack.WordAlloc.wordStateEqRel source target ∧
    ssaLocalsRel next map source.locals target.locals ∧ isAllocVar next ∧
    everyVarHOL (fun key => decide (key < next)) body = true ∧
    ssaMapOK next map ∧ ltOK tables →
    SSAQuantitativeAllowance SP TP body source target map next tables entry

/-- Only a root loop has a setup allowance; enclosing executed control nodes
fund their immediate children separately at the actual SSA map/counter. -/
def ssaRootEntryAllowance (TP : WordLangProgHOL (BitVec 64) → Nat)
    (p : WordLangProgHOL (BitVec 64)) (map : Spt Nat) (next : Nat) : Nat :=
  match p with
  | .loop names _ exits => ssaReconciliationPrice TP (loopSetup (width := 64) names exits map next).1
  | _ => 0

theorem ssa_quantitative_allowance_zero {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat) (p : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) :
    SSAQuantitativeAllowance SP TP p source target map next tables 0 ↔
      SSAQuantitativeSimulation SP TP p source target map next tables := by
  simp only [SSAQuantitativeAllowance,SSAQuantitativeSimulation,Nat.add_zero]


#print axioms ssa_quantitative_allowance_zero
end InitECandidate.Runtime.FineCost
