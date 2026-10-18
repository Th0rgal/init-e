import InitECandidate.Runtime.U256FromBeTailCallFrame
import InitECandidate.Runtime.TxScalarU256AfterFieldBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Size rejection and either conversion path retain all memory and globals. -/
theorem txScalarU256_after_field_frame : RuntimeFrame txScalarU256AfterField := by
  rw [source_txScalarU256_after_field]
  exact runtimeFrame_seq _ _ (runtimeFrame_readOnly _ (by rfl)) (u256FromBe_tailCall_frame _)

#print axioms txScalarU256_after_field_frame
end InitECandidate.Runtime
