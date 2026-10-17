import InitECandidate.Runtime.HashNewKeysAllocation
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
import InitECandidate.Runtime.AllocationFailureDeclarationNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Rejected keys-array allocation skips its pointer store and every later
constructor allocation. Argument multiplication uses the actual word semantics. -/
theorem evaluate_htabNew_keys_allocation_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer stride capacity : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (rejected : ((33806089496 : BitVec 64) - pointer).toNat < (capacity * stride).toNat)
    (ticks : 2 ≤ state.clock) :
    (evaluateHOLFiniteState state htabNewAfterHeader).1 ≠ none ∧
      (evaluateHOLFiniteState state htabNewAfterHeader).1 ≠ some .timeOut ∧
      (∀ value, (evaluateHOLFiniteState state htabNewAfterHeader).1 ≠ some (.returned value)) ∧
      (evaluateHOLFiniteState state htabNewAfterHeader).2.clock = state.clock - 2 := by
  let argument : ExpHOL 64 := .panop .mul [.var .local (ofString "cap"),.var .local (ofString "stride")]
  let continuation : ProgHOL 64 := .seq (.store (hashLocalAddress (ofString "t") 32) (.var .local (ofString "keys"))) htabNewValuesAllocation
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word (capacity * stride))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,strideLocal,panOpHOL,valueIsWord,valueWord]
  have failure := evaluate_alloc_request_failure_declaration state argument pointer (capacity * stride) (ofString "keys") .one continuation args code heap rejected
  have noTimeout := evaluate_alloc_request_failure_declaration_no_timeout state argument pointer (capacity * stride) (ofString "keys") .one continuation args code heap rejected ticks
  rw [source_htabNew_keys_allocation]
  refine ⟨failure.1,noTimeout,?_,failure.2⟩
  intro value
  exact evaluate_alloc_request_failure_declaration_no_return state argument pointer (capacity * stride) (ofString "keys") .one continuation value args code heap rejected

#print axioms evaluate_htabNew_keys_allocation_failure
end InitECandidate.Runtime
