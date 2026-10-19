import InitECandidate.Runtime.WitnessExtensionSource
import InitECandidate.Runtime.NodeNewExtUniformBound
import InitECandidate.Runtime.MptFailCallBound
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_extension_failure_bounded :
    ProgBounded (.call (some (none,none)) (ofString "mpt_fail") [.const 8]) 1 := by
  intro F s code budget
  have bounded := evaluate_mptFail_call_bounded s (.const 8) 8 code (by omega)
    (by rw [evalListHOLFinite_eq_toExact]; rfl)
  exact ⟨by rw [bounded.1]; omega,by rw [bounded.1]; omega,bounded.2.1⟩

theorem witness_extension_guard_bounded (condition : ExpHOL 64) :
    ProgBounded (.ite condition (.call (some (none,none)) (ofString "mpt_fail") [.const 8]) .skip) 1 :=
  ProgBounded.ite condition witness_extension_failure_bounded
    (ProgBounded.weaken (ProgBounded.straight .skip rfl) (by omega))

theorem witness_extension_stores_bounded : ProgBounded witnessExtensionStores 0 := by
  apply ProgBounded.straight
  rw [source_witness_extension_stores]
  rfl

theorem witness_extension_constructor_bounded : ProgBounded witnessExtensionConstructor 3 := by
  rw [source_witness_extension_constructor]
  exact ProgBounded.decCall node_new_ext_fun_bounded (ofString "ex") .one
    witnessExtensionArguments witness_extension_stores_bounded

theorem witness_extension_kind_scope_bounded : ProgBounded witnessExtensionKindScope 4 := by
  rw [source_witness_extension_kind_scope]
  exact ProgBounded.dec _ _ _
    (ProgBounded.seq (witness_extension_guard_bounded witnessExtensionKindCheck)
      witness_extension_constructor_bounded)

/-- The actual extension unwind is bounded on every outcome, including
inaccessible guards, allocation rejection and failed record stores. -/
theorem witness_extension_uniform_bounded : ProgBounded witnessUnwindExtension 5 := by
  rw [source_witness_extension]
  exact ProgBounded.seq (witness_extension_guard_bounded _) witness_extension_kind_scope_bounded

theorem runBounded_witness_extension {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) (budget : 5 ≤ s.clock) :
    RunBounded s witnessUnwindExtension 5 :=
  RunBounded.ofProg witness_extension_uniform_bounded code budget

#print axioms witness_extension_failure_bounded
#print axioms witness_extension_stores_bounded
#print axioms witness_extension_constructor_bounded
#print axioms witness_extension_kind_scope_bounded
#print axioms witness_extension_uniform_bounded
#print axioms runBounded_witness_extension
end InitECandidate.Runtime
