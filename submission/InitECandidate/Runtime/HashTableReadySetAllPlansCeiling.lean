import InitECandidate.Runtime.HashTableReadySetCallAllPlansSupported
import InitECandidate.Runtime.HashSetSupportedCostCeiling
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_call_supported_all_plans_ceiling {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (pointerAligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (ticks : 2 ^ 72 ≤ state.clock)
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
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument])).2.clock +
      2 ^ 72 ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock := by
  have ceiling := hashSetSupportedCost_le_ceiling capacity keyLength items capacityBound supported
    (Nat.le_of_lt invariant.live.arrays.room)
  have bounded := invariant.set_call_supported_all_plans_bounded state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
    strideBound pointerAligned pointerBound capacityBound
    (by change hashSetSupportedCost capacity keyLength items ≤ state.clock; omega)
    heap domain tableArgument keyArgument valueArgument arguments capacityLarge keyAligned sourceWordDomain sourceByteDomain
  unfold hashSetSupportedCost at ceiling
  exact ⟨by have cost := bounded.1; omega,bounded.2⟩

#print axioms HashTableReady.set_call_supported_all_plans_ceiling
end InitECandidate.Runtime
