import InitECandidate.Runtime.HashGrowFailureBody
import InitECandidate.Runtime.DiscardCallClock
import InitECandidate.Runtime.OriginalHashGrowCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_htabGrow_allocation_failure_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity stride keys values order count : BitVec 64)
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain40 : state.memaddrs (table + 40)) (cell40 : state.memory (table + 40) = .word values)
    (domain56 : state.memaddrs (table + 56)) (cell56 : state.memory (table + 56) = .word order)
    (domain24 : state.memaddrs (table + 24)) (cell24 : state.memory (table + 24) = .word count)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 5 ≤ state.clock)
    (notSafe : ¬ AllocationPlanSafe pointer
      [(capacity * 2) * stride,(capacity * 2) * 8,capacity * 2,(capacity * 2) * 8,(capacity * 2) * 8])
    (argument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word table)]) :
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [argument])).2.clock + 7 ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [argument])).2.clock ≤ state.clock := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "t",.val (.word table))
  let entry := callEntryStateHOLFinite state callee
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have failure := evaluate_source_htabGrow_allocation_failure entry table capacity stride keys values order count t
    domain16 cell16 domain8 cell8 domain32 cell32 domain40 cell40 domain56 cell56 domain24 cell24
    pointer code heap pointerBound (by change 4 ≤ state.clock - 1; omega) notSafe
  have installed : state.code.lookup (ofString "htab_grow") =
      some ([(ofString "t",.one)],sourceFunctionBody Guest.guestFn_htab_grow,.one) := by
    rw [code]; exact originalRuntimeCode_hashGrow_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "htab_grow") (ofString "t")
    (sourceFunctionBody Guest.guestFn_htab_grow) table installed
  have callClock := evaluate_discard_call_body_clock state
    (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_grow)).2 (ofString "htab_grow")
    [argument] [.val (.word table)] (sourceFunctionBody Guest.guestFn_htab_grow) callee .one
    (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_grow)).1 arguments lookup (by omega) rfl
  rw [callClock]
  have cost := failure.2.1
  have remaining := failure.2.2
  change state.clock - 1 ≤ (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_grow)).2.clock + 6 at cost
  change (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_grow)).2.clock ≤ state.clock - 1 at remaining
  exact ⟨by omega,by omega⟩

#print axioms evaluate_htabGrow_allocation_failure_call
end InitECandidate.Runtime
