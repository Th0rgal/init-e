import InitECandidate.Runtime.HashTableSetCallAboveThresholdOtherValuesIn
import InitECandidate.Runtime.HashTableSetNoGrowthOtherValuesIn
import InitECandidate.Runtime.HashTableSetUnsafeOtherValuesIn
import InitECandidate.Runtime.HashTableValuesInSetCallNoGrowth
import InitECandidate.Runtime.HashTableValuesInSetNoGrowth
import InitECandidate.Runtime.HashTableArraysFindSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_call_all_plans_other_values_in {F : Type}
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
    (ticks : 2 ^ 74 ≤ state.clock)
    (domain : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride) → ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (success : (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 = none) :
    HashTableValuesIn otherTable targets (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2 := by
  have u := initialReady.live.arrays.usedBefore
  have o := initialReady.live.arrays.orderBefore
  have e := initialReady.live.arrays.endBound
  have room := initialReady.live.arrays.room
  have capBound : capacity.toNat ≤ 33806089496 := by omega
  have keyBound : keyLength.toNat ≤ 52 := by rcases supported with h | h | h <;> simp [h]
  have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
    rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
    change capacity.toNat * 2 = 2 * capacity.toNat
    omega
  have product := Nat.mul_le_mul (show items.toNat ≤ 33806089496 by omega)
    (show (capacity * (2 : BitVec 64)).toNat + keyLength.toNat + 4 ≤ 67612179048 by rw [doubled]; omega)
  have bound : 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 13 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ 2 ^ 74 := by rw [doubled]; rw [doubled] at product; omega
  by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
  · obtain ⟨post,run,_,postRegistered,_⟩ := initialReady.set_call_no_growth_other_values_in state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
      keyAligned sourceWordDomain sourceByteDomain below (by omega) tableArgument keyArgument valueArgument arguments
      otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady targets registered separate
    rw [run]
    exact postRegistered
  · by_cases safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)
    · obtain ⟨post,run,postRegistered,_⟩ := initialReady.set_call_above_threshold_other_values_in state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady targets registered separate
        strideBound safe (by omega) (domain safe) tableArgument keyArgument valueArgument arguments (by omega) capacityLarge keyAligned sourceWordDomain sourceByteDomain
      rw [run]
      exact postRegistered
    · exact initialReady.set_call_unsafe_growth_other_values_in state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain (by omega)
        initialReady.live.frontier.heap initialReady.live.frontier.bounded safe (by omega)
        otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady targets registered separate success

#print axioms HashTableReady.set_call_all_plans_other_values_in
end InitECandidate.Runtime
