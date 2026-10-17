import InitECandidate.Runtime.HashTableReadySetAllPlansSupportedNoTimeout
import InitECandidate.Runtime.OriginalHashSetCode
import InitECandidate.Runtime.DiscardCallClock
import InitECandidate.Runtime.DiscardCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_call_supported_all_plans_no_timeout {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (pointerAligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 13 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some .timeOut ∧
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument])).2.clock +
      2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 13 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have vt : ofString "value" ≠ ofString "t" := by decide
  have vk : ofString "value" ≠ ofString "key" := by decide
  have kt : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vt,kt]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vk]
  have v : entry.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryValid := invariant.after_read state entry keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have bounded := entryValid.set_body_supported_all_plans_no_timeout entry keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
     strideBound pointerAligned pointerBound capacityBound
    (by change 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock - 1; omega)
    heap domain t k v capacityLarge keyAligned sourceWordDomain sourceByteDomain
  have installed : state.code.lookup (ofString "htab_set") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_htab_set,.one) := by
    rw [invariant.live.arrays.code]; exact originalRuntimeCode_hashSet_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") (sourceFunctionBody Guest.guestFn_htab_set)
    table key value (by decide) (by decide) (by decide) installed
  have callClock := evaluate_discard_call_body_clock state
    (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_set)).2 (ofString "htab_set")
    [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
    (sourceFunctionBody Guest.guestFn_htab_set) callee .one
    (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_set)).1 arguments lookup (by omega) rfl
  have noTimeout := evaluate_discard_call_body_no_timeout state
    (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_set)).2 (ofString "htab_set")
    [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
    (sourceFunctionBody Guest.guestFn_htab_set) callee .one
    (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_set)).1 arguments lookup (by omega) rfl bounded.2.1
  refine ⟨noTimeout,?_⟩
  rw [callClock]
  have cost := bounded.2.2.1
  have remaining := bounded.2.2.2
  change state.clock - 1 ≤ (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_set)).2.clock +
    2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) at cost
  change (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_set)).2.clock ≤ state.clock - 1 at remaining
  exact ⟨by omega,by omega⟩

#print axioms HashTableReady.set_call_supported_all_plans_no_timeout
end InitECandidate.Runtime
