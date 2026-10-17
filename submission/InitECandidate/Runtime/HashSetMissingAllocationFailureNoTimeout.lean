import InitECandidate.Runtime.HashGrowFailureCallNoTimeout
import InitECandidate.Runtime.HashGrowFailureCall
import InitECandidate.Runtime.HashGrowFailureCallTerminal
import InitECandidate.Runtime.HashSetGrowthTrue
import InitECandidate.Runtime.AllocationFailureTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashSet_missing_allocation_failure_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity stride keys values order count : BitVec 64)
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain40 : state.memaddrs (table + 40)) (cell40 : state.memory (table + 40) = .word values)
    (domain56 : state.memaddrs (table + 56)) (cell56 : state.memory (table + 56) = .word order)
    (domain24 : state.memaddrs (table + 24)) (cell24 : state.memory (table + 24) = .word count)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 7 ≤ state.clock)
    (notSafe : ¬ AllocationPlanSafe pointer
      [(capacity * 2) * stride,(capacity * 2) * 8,capacity * 2,(capacity * 2) * 8,(capacity * 2) * 8])
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (loadFactor : capacity.toNat < (count.toNat + 1) * 2)
    (room : count.toNat < capacity.toNat) (capacityBound : capacity.toNat ≤ 33806089496) :
    evaluateHOLFiniteState state hashSetMissing =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) ∧
    (evaluateHOLFiniteState state hashSetMissing).1 ≠ none ∧
    (evaluateHOLFiniteState state hashSetMissing).1 ≠ some .timeOut ∧
    state.clock ≤ (evaluateHOLFiniteState state hashSetMissing).2.clock + 7 ∧
    (evaluateHOLFiniteState state hashSetMissing).2.clock ≤ state.clock := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "t")] = some [.val (.word table)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal]
  have bounded := evaluate_htabGrow_allocation_failure_call state table capacity stride keys values order count
    domain16 cell16 domain8 cell8 domain32 cell32 domain40 cell40 domain56 cell56 domain24 cell24
    pointer code heap pointerBound (by omega) notSafe (.var .local (ofString "t")) arguments
  have terminal := evaluate_htabGrow_failure_call_terminal state table capacity stride keys values order count
    domain16 cell16 domain8 cell8 domain32 cell32 domain40 cell40 domain56 cell56 domain24 cell24
    pointer code heap pointerBound (by omega) notSafe (.var .local (ofString "t")) arguments
  have noTimeout := evaluate_htabGrow_failure_call_no_timeout state table capacity stride keys values order count
    domain16 cell16 domain8 cell8 domain32 cell32 domain40 cell40 domain56 cell56 domain24 cell24
    pointer code heap pointerBound clock notSafe (.var .local (ofString "t")) arguments
  have selected := evaluate_hashSet_growth_selected state table capacity count tableLocal domain16 cell16 domain24 cell24 loadFactor room capacityBound
  have stopped := evaluate_sequence_stops state
    (.ite hashSetGrowthCondition (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) .skip)
    (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]) (.return (.const 0)))
    (by rw [selected]; exact terminal) (by rw [selected]; exact bounded.2)
  have run : evaluateHOLFiniteState state hashSetMissing =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) := by
    rw [source_hashSet_missing]
    exact stopped.trans selected
  exact ⟨run,by rw [run]; exact terminal,by rw [run]; exact noTimeout,by rw [run]; exact bounded.1,by rw [run]; exact bounded.2⟩

#print axioms evaluate_hashSet_missing_allocation_failure_no_timeout
end InitECandidate.Runtime
