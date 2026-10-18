import InitECandidate.Runtime.AllocationUniformBound
import InitECandidate.Runtime.OriginalAllocationCode
import InitECandidate.Runtime.LookupCodeInstalledBody
import InitECandidate.Runtime.PanUniformCalleeCallBound
import InitECandidate.Runtime.PanSequenceCodeBound
import InitECandidate.Runtime.ByteStraightLine
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_alloc_uniform_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 2 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "alloc") arguments)
    state.clock ≤ result.2.clock + 2 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "alloc") destination arguments 1 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "alloc") [(ofString "n",.one)]
    (sourceFunctionBody Guest.guestFn_alloc) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_allocation_lookup) found
  rw [same]
  have bound := evaluate_source_alloc_uniform_bounded (callEntryStateHOLFinite state locals) code
    (by change 1 ≤ state.clock - 1; omega)
  exact ⟨bound.1,bound.2.1,bound.2.2.1⟩

/-- A checked source fragment containing only ordinary straight-line work and
allocator calls. Every allocator rejection and expression/access error is covered. -/
inductive AllocationFragment : ProgHOL 64 → Type
  | straight (program : ProgHOL 64) (supported : byteStraightLine program = true) : AllocationFragment program
  | allocation (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
      AllocationFragment (.call (some (destination,none)) (ofString "alloc") arguments)
  | sequence {first tail : ProgHOL 64} (a : AllocationFragment first) (b : AllocationFragment tail) :
      AllocationFragment (.seq first tail)
  | conditional (condition : ExpHOL 64) {yes no : ProgHOL 64}
      (a : AllocationFragment yes) (b : AllocationFragment no) : AllocationFragment (.ite condition yes no)

def AllocationFragment.cost {program : ProgHOL 64} : AllocationFragment program → Nat
  | .straight _ _ => 0
  | .allocation _ _ => 2
  | .sequence a b => a.cost + b.cost
  | .conditional _ a b => a.cost + b.cost

theorem AllocationFragment.bounded {program : ProgHOL 64} (fragment : AllocationFragment program)
    {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : fragment.cost ≤ state.clock) :
    let result := evaluateHOLFiniteState state program
    state.clock ≤ result.2.clock + fragment.cost ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  induction fragment generalizing state with
  | straight program supported =>
    have same := clockPreserving_of_byteStraightLine (F := F) program supported state
    exact ⟨by simp [AllocationFragment.cost,same],by simp [same],evaluate_byteStraightLine_no_timeout program supported state⟩
  | allocation destination arguments => exact evaluate_alloc_uniform_call_bounded state destination arguments code budget
  | sequence a b firstBound tailBound =>
    exact evaluate_sequence_code_bounded state _ _ a.cost b.cost
      (firstBound state code (by change a.cost + b.cost ≤ state.clock at budget; omega))
      (fun next installed enough => tailBound next (installed.trans code) enough) budget
  | conditional condition a b yesBound noBound =>
    have y := yesBound state code (by change a.cost + b.cost ≤ state.clock at budget; omega)
    have n := noBound state code (by change a.cost + b.cost ≤ state.clock at budget; omega)
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact ⟨by have h := n.1; change state.clock ≤ _ + (a.cost + b.cost); omega,n.2⟩
      · exact ⟨by have h := y.1; change state.clock ≤ _ + (a.cost + b.cost); omega,y.2⟩
    · exact ⟨by simp,by simp,by simp⟩

#print axioms evaluate_alloc_uniform_call_bounded
#print axioms AllocationFragment.bounded
end InitECandidate.Runtime
