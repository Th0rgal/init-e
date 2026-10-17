import InitECandidate.Runtime.HashNewArrayFailures
import InitECandidate.Runtime.HashNewZeroRuntimePrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- If the order allocation succeeds and the reverse allocation is rejected,
the actual post-zero constructor suffix exits in three source clocks. -/
theorem evaluate_htabNew_order_then_reverse_failure {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer table capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : 3 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (request : capacity * 8 ≤ (33806089496 : BitVec 64) - pointer)
    (finish : (allocationEnd pointer (capacity * 8)).toNat ≤ 33806089496)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain56 : state.memaddrs (table + 56))
    (rejected : ((33806089496 : BitVec 64) - allocationEnd pointer (capacity * 8)).toNat < (capacity * 8).toNat) :
    (evaluateHOLFiniteState state htabNewAfterZero).1 ≠ none ∧
      (evaluateHOLFiniteState state htabNewAfterZero).1 ≠ some .timeOut ∧
      (∀ value, (evaluateHOLFiniteState state htabNewAfterZero).1 ≠ some (.returned value)) ∧
      (evaluateHOLFiniteState state htabNewAfterZero).2.clock = state.clock - 3 := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,run,clock,locals,_,_,nextHeap,nextCode,_,_⟩ :=
    evaluate_allocation_pointer_store state (ofString "order") (ofString "t") _ pointer (capacity * 8)
      table 56 htabNewFinalAllocation (by decide) args code (by omega) heap request finish tableLocal domain56
  have capAfter : ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [locals]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "order" ≠ ofString "cap" from by decide] using capLocal
  have failure := evaluate_htabNew_reverse_allocation_failure ready _ capacity (nextCode.trans code) nextHeap capAfter rejected (by omega)
  have actualRun : evaluateHOLFiniteState state htabNewAfterZero =
      (let output := evaluateHOLFiniteState ready htabNewFinalAllocation;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "order",state.locals.lookup (ofString "order"))})) := by
    rw [source_htabNew_order_tail]
    exact run
  rw [actualRun]
  exact ⟨failure.1,failure.2.1,failure.2.2.1,by dsimp only; rw [failure.2.2.2,clock]; omega⟩

/-- Occupancy clearing followed by order-array rejection terminates within
capacity+3 clocks, without requiring space for later arrays. -/
theorem evaluate_htabNew_zero_then_order_failure {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer table used capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 3 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (small : used.toNat + capacity.toNat ≤ 33806089496) (aligned : used.toNat % 8 = 0)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain48 : state.memaddrs (table + 48))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (used + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (panByteAlignHOL (used + BitVec.ofNat 64 offset)))
    (rejected : ((33806089496 : BitVec 64) - pointer).toNat < (capacity * 8).toNat) :
    let output := evaluateHOLFiniteState state htabNewUsedBody;
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      state.clock ≤ output.2.clock + capacity.toNat + 3 ∧ output.2.clock ≤ state.clock := by
  obtain ⟨ready,run,cost,remaining,locals,globals,nextCode,domain,_⟩ :=
    evaluate_htabNew_zero_runtime_prefix state table used capacity htabNewAfterZero code (by omega)
      small aligned tableLocal usedLocal capLocal domain48 wordDomain byteDomain
  have failure := evaluate_htabNew_order_allocation_failure ready pointer capacity (nextCode.trans code)
    (by rw [globals]; exact heap) (by rw [locals]; exact capLocal) rejected (by omega)
  dsimp only
  rw [source_htabNew_zero_prefix,run]
  exact ⟨failure.1,failure.2.1,failure.2.2.1,by rw [failure.2.2.2]; omega,by rw [failure.2.2.2]; omega⟩

/-- Occupancy clearing followed by reverse-array rejection terminates within
capacity+4 clocks, without requiring space for later arrays. -/
theorem evaluate_htabNew_zero_then_reverse_failure {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer table used capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 4 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (small : used.toNat + capacity.toNat ≤ 33806089496) (aligned : used.toNat % 8 = 0)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain48 : state.memaddrs (table + 48))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (used + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (panByteAlignHOL (used + BitVec.ofNat 64 offset)))
    (request : capacity * 8 ≤ (33806089496 : BitVec 64) - pointer)
    (finish : (allocationEnd pointer (capacity * 8)).toNat ≤ 33806089496)
    (domain56 : state.memaddrs (table + 56))
    (rejected : ((33806089496 : BitVec 64) - allocationEnd pointer (capacity * 8)).toNat < (capacity * 8).toNat) :
    let output := evaluateHOLFiniteState state htabNewUsedBody;
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      state.clock ≤ output.2.clock + capacity.toNat + 4 ∧ output.2.clock ≤ state.clock := by
  obtain ⟨ready,run,cost,remaining,locals,globals,nextCode,domain,_⟩ :=
    evaluate_htabNew_zero_runtime_prefix state table used capacity htabNewAfterZero code (by omega)
      small aligned tableLocal usedLocal capLocal domain48 wordDomain byteDomain
  have failure := evaluate_htabNew_order_then_reverse_failure ready pointer table capacity (nextCode.trans code) (by omega)
    (by rw [globals]; exact heap) request finish (by rw [locals]; exact tableLocal)
    (by rw [locals]; exact capLocal) (by rw [domain]; exact domain56) rejected
  dsimp only
  rw [source_htabNew_zero_prefix,run]
  exact ⟨failure.1,failure.2.1,failure.2.2.1,by rw [failure.2.2.2]; omega,by rw [failure.2.2.2]; omega⟩

#print axioms evaluate_htabNew_order_then_reverse_failure
#print axioms evaluate_htabNew_zero_then_order_failure
#print axioms evaluate_htabNew_zero_then_reverse_failure
end InitECandidate.Runtime
