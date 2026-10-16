import InitECandidate.Runtime.HashGrowHeaderLoads
import InitECandidate.Runtime.HashGrowUnsafeAllocationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_source_htabGrow_allocation_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity stride keys values order count : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain40 : state.memaddrs (table + 40)) (cell40 : state.memory (table + 40) = .word values)
    (domain56 : state.memaddrs (table + 56)) (cell56 : state.memory (table + 56) = .word order)
    (domain24 : state.memaddrs (table + 24)) (cell24 : state.memory (table + 24) = .word count)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 4 ≤ state.clock)
    (notSafe : ¬ AllocationPlanSafe pointer
      [(capacity * 2) * stride,(capacity * 2) * 8,capacity * 2,(capacity * 2) * 8,(capacity * 2) * 8]) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_grow)).1 ≠ none ∧
    state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_grow)).2.clock + 6 ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_grow)).2.clock ≤ state.clock := by
  obtain ⟨entered,headerRun,_,strideLocal,_,_,_,_,capacityLocal,_,globals,postCode,_,_,ticks,_⟩ :=
    evaluate_htabGrow_header_loads state table capacity stride keys values order count tableLocal
      domain16 cell16 domain8 cell8 domain32 cell32 domain40 cell40 domain56 cell56 domain24 cell24
  have heapEntry : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := by
    rw [globals]; exact heap
  have failure := evaluate_hashGrow_unsafe_allocations_bounded entered pointer (capacity * 2) stride
    (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0))))
    (postCode.trans code) heapEntry capacityLocal strideLocal pointerBound (by rw [ticks]; exact clock) notSafe
  rw [source_htabGrow_header_prefix,headerRun]
  dsimp only
  refine ⟨failure.1,?_,?_⟩
  · change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + 6
    rw [← ticks]
    exact failure.2.1
  · change (evaluateHOLFiniteState entered _).2.clock ≤ state.clock
    rw [← ticks]
    exact failure.2.2

#print axioms evaluate_source_htabGrow_allocation_failure
end InitECandidate.Runtime
