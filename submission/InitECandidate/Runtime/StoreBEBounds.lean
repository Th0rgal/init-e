import InitECandidate.Runtime.OriginalStoreBE32Code
import InitECandidate.Runtime.OriginalStoreBE64Code
import InitECandidate.Runtime.Bswap64CallBound
import InitECandidate.Runtime.AllocationFragmentBound
import InitECandidate.Runtime.ByteStraightCalleeCallBound
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem storeBE32_byteStraight : byteStraightLine (sourceFunctionBody Guest.guestFn_st_be32) = true := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_storeBE32_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "st_be32") arguments)
    state.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  apply evaluate_byteStraightCallee_call_bounded state (ofString "st_be32") destination arguments ?_ budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "st_be32")
    [(ofString "p",.one),(ofString "v",.one)] (sourceFunctionBody Guest.guestFn_st_be32) body .one returnShape
    values locals (by rw [code]; exact originalRuntimeCode_storeBE32_lookup) found
  rw [same]
  exact storeBE32_byteStraight

def storeBE64AlignedTail : ProgHOL 64 :=
  .seq (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) (.return (.const 0))
def storeBE64AlignedBranch : ProgHOL 64 :=
  .decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")] storeBE64AlignedTail
def storeBE64Guard : ProgHOL 64 :=
  .ite (.cmp .equal (.op .and [.var .local (ofString "p"),.const 7]) (.const 0)) storeBE64AlignedBranch .skip
def storeBE64FirstArguments : List (ExpHOL 64) :=
  [.var .local (ofString "p"),.shift .lsr (.var .local (ofString "v")) (.const 32)]
def storeBE64LastArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "p"),.const 4],.var .local (ofString "v")]
def storeBE64Fallback : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "st_be32") storeBE64FirstArguments)
    (.seq (.call (some (none,none)) (ofString "st_be32") storeBE64LastArguments) (.return (.const 0)))

theorem source_storeBE64_body : sourceFunctionBody Guest.guestFn_st_be64 =
    .seq storeBE64Guard storeBE64Fallback := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_storeBE64_guard_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state storeBE64Guard
    state.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have aligned := evaluate_bswap64_call_bounded state (ofString "w") .one [.var .local (ofString "v")]
    storeBE64AlignedTail 0 code
    (by intro current installed _; exact (AllocationFragment.straight storeBE64AlignedTail (by rfl)).bounded current installed (by simp [AllocationFragment.cost]))
    budget
  rw [storeBE64Guard,evaluateHOLFiniteState_ite]
  split
  · split
    · simp [evaluateHOLFiniteState_skip]
    · exact aligned
  · simp

/-- Uniform runtime includes the aligned byte-swap path, byte fallback,
invalid arguments, inaccessible stores, and return-shape failures. -/
theorem evaluate_storeBE64_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 3 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_st_be64)
    state.clock ≤ evaluated.2.clock + 3 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_storeBE64_body]
  apply evaluate_sequence_code_bounded state _ _ 1 2 (evaluate_storeBE64_guard_bounded state code (by omega)) ?_ budget
  intro next installed enough
  unfold storeBE64Fallback
  apply evaluate_sequence_code_bounded next _ _ 1 1
    (evaluate_storeBE32_call_bounded next none storeBE64FirstArguments (installed.trans code) (by omega)) ?_ enough
  intro last lastCode lastBudget
  exact evaluate_sequence_straight_bounded last _ (.return (.const 0)) 1
    (evaluate_storeBE32_call_bounded last none storeBE64LastArguments (lastCode.trans (installed.trans code)) lastBudget) (by rfl)

theorem evaluate_storeBE64_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 4 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "st_be64") arguments)
    state.clock ≤ evaluated.2.clock + 4 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "st_be64") destination arguments 3 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "st_be64")
    [(ofString "p",.one),(ofString "v",.one)] (sourceFunctionBody Guest.guestFn_st_be64) body .one returnShape
    values locals (by rw [code]; exact originalRuntimeCode_storeBE64_lookup) found
  rw [same]
  exact evaluate_storeBE64_body_bounded (callEntryStateHOLFinite state locals) code (by change 3 ≤ state.clock - 1; omega)

#print axioms evaluate_storeBE32_call_bounded
#print axioms source_storeBE64_body
#print axioms evaluate_storeBE64_guard_bounded
#print axioms evaluate_storeBE64_body_bounded
#print axioms evaluate_storeBE64_call_bounded
end InitECandidate.Runtime
