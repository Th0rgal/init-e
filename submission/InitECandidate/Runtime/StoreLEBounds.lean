import InitECandidate.Runtime.OriginalStoreLE32Code
import InitECandidate.Runtime.OriginalStoreLE64Code
import InitECandidate.Runtime.ByteStraightCalleeCallBound
import InitECandidate.Runtime.LookupCodeInstalledBody
import InitECandidate.Runtime.PanSequenceCodeBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.PanUniformCalleeCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem storeLE32_byteStraight : byteStraightLine (sourceFunctionBody Guest.guestFn_st_le32) = true := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original 32-bit byte serializer adds only its call-entry clock. -/
theorem evaluate_storeLE32_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "st_le32") arguments)
    state.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  apply evaluate_byteStraightCallee_call_bounded state (ofString "st_le32") destination arguments ?_ budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "st_le32")
    [(ofString "p",.one),(ofString "v",.one)] (sourceFunctionBody Guest.guestFn_st_le32) body .one returnShape
    values locals (by rw [code]; exact originalRuntimeCode_storeLE32_lookup) found
  rw [same]
  exact storeLE32_byteStraight

def storeLE64FirstArguments : List (ExpHOL 64) := [.var .local (ofString "p"),.var .local (ofString "v")]
def storeLE64LastArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "p"),.const 4],.shift .lsr (.var .local (ofString "v")) (.const 32)]

theorem source_storeLE64_body : sourceFunctionBody Guest.guestFn_st_le64 =
    .seq (.call (some (none,none)) (ofString "st_le32") storeLE64FirstArguments)
      (.seq (.call (some (none,none)) (ofString "st_le32") storeLE64LastArguments) (.return (.const 0))) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original 64-bit serializer body has two bounded 32-bit calls. -/
theorem evaluate_storeLE64_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_st_le64)
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_storeLE64_body]
  apply evaluate_sequence_code_bounded state _ _ 1 1
    (evaluate_storeLE32_call_bounded state none storeLE64FirstArguments code (by omega)) ?_ budget
  intro next kept enough
  exact evaluate_sequence_straight_bounded next _ (.return (.const 0)) 1
    (evaluate_storeLE32_call_bounded next none storeLE64LastArguments (kept.trans code) enough) (by rfl)

theorem evaluate_storeLE64_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 3 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "st_le64") arguments)
    state.clock ≤ evaluated.2.clock + 3 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "st_le64") destination arguments 2 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "st_le64")
    [(ofString "p",.one),(ofString "v",.one)] (sourceFunctionBody Guest.guestFn_st_le64) body .one returnShape
    values locals (by rw [code]; exact originalRuntimeCode_storeLE64_lookup) found
  rw [same]
  exact evaluate_storeLE64_body_bounded (callEntryStateHOLFinite state locals) code (by change 2 ≤ state.clock - 1; omega)

#print axioms evaluate_storeLE32_call_bounded
#print axioms evaluate_storeLE64_body_bounded
#print axioms evaluate_storeLE64_call_bounded
end InitECandidate.Runtime
