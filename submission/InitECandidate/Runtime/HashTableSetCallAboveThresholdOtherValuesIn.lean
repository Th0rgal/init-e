import InitECandidate.Runtime.HashTableSetAboveThresholdOtherValuesIn
import InitECandidate.Runtime.HashTableValuesInSetCallNoGrowth
import InitECandidate.Runtime.HashTableValuesInSetNoGrowth
import InitECandidate.Runtime.HashTableArraysFindSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_call_above_threshold_other_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initialReady : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn otherTable targets state)
    (separate : ∀ address : BitVec 64,
      tablePhysicalRegion table keys stride capacity used values order orderPos address →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address)
    (strideBound : stride.toNat ≤ 56)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 13 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (loadFactor : capacity.toNat < (items.toNat + 1) * 2)
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableValuesIn otherTable targets post ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 13 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
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
  have entryReady := initialReady.after_read state entry keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have entryOther := otherReady.after_read state entry otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl
  obtain ⟨post,body,_,postRegistered,cost,remaining,code,addresses,endian⟩ :=
    entryReady.set_above_threshold_other_values_in entry keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
      otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits entryOther targets (registered.after_read rfl rfl rfl) separate strideBound safePlan
      (by change 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock - 1; omega)
      domain t k v loadFactor capacityLarge keyAligned sourceWordDomain sourceByteDomain
  have installed : state.code.lookup (ofString "htab_set") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_htab_set,.one) := by
    rw [initialReady.live.arrays.code]; exact originalRuntimeCode_hashSet_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    (sourceFunctionBody Guest.guestFn_htab_set) table key value (by decide) (by decide) (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_set")
    [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
    (sourceFunctionBody Guest.guestFn_htab_set) callee .one (.val (.word 0)) post arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  let restored := {post with locals := state.locals}
  refine ⟨restored,call,postRegistered.after_read rfl rfl rfl,?_,?_,rfl,code,addresses,endian⟩
  · change state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 13 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4)
    change state.clock - 1 ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms HashTableReady.set_call_above_threshold_other_values_in
end InitECandidate.Runtime
