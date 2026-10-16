import InitECandidate.Runtime.HashTableSetCallAllPlansBound32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashSetClockCeiling32 : Nat :=
  6 * 33806089496 + 45 + 33806089496 * (2 * 33806089496 + 36)

/-- Array geometry bounds capacity even before considering the item count. -/
theorem HashTableArraysInvariant32.capacity_bounded {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state) :
    capacity.toNat ≤ 33806089496 := by
  have usedBefore := invariant.usedBefore
  have orderBefore := invariant.orderBefore
  have limit := invariant.endBound
  omega

theorem hashSet_clock_expression_bounded (capacity items : BitVec 64)
    (capacityBound : capacity.toNat ≤ 33806089496) (itemsBound : items.toNat ≤ capacity.toNat) :
    2 * capacity.toNat + 2 * (capacity * 2).toNat + 45 + items.toNat * ((capacity * 2).toNat + 36) ≤ hashSetClockCeiling32 := by
  have doubled : (capacity * (2 : BitVec 64)).toNat = capacity.toNat * 2 := by
    exact BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  rw [doubled]
  have product := Nat.mul_le_mul (show items.toNat ≤ 33806089496 by omega)
    (show capacity.toNat * 2 + 36 ≤ 2 * 33806089496 + 36 by omega)
  unfold hashSetClockCeiling32
  omega

#print axioms HashTableArraysInvariant32.capacity_bounded
#print axioms hashSet_clock_expression_bounded
theorem HashTableArraysInvariant32.set_call_uniform_bounded {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (entries : HashOrderEntriesBound order capacity items state)
    (allocated : orderPos.toNat + capacity.toNat * 8 ≤ pointer.toNat)
    (strideBound : stride.toNat ≤ 56) (pointerAligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (ticks : hashSetClockCeiling32 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument])).2.clock + hashSetClockCeiling32 ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock := by
  have capacityBound := invariant.capacity_bounded state table keys stride capacity used values order orderPos items bits
  have expression := hashSet_clock_expression_bounded capacity items capacityBound (Nat.le_of_lt invariant.room)
  have bounded := invariant.set_call_all_plans_bounded state table pointer keys stride capacity used values order orderPos items key value bits
    entries allocated strideBound pointerAligned pointerBound capacityBound (by omega) heap domain tableArgument keyArgument valueArgument arguments
    capacityLarge keyAligned sourceWordDomain sourceByteDomain
  exact ⟨by have := bounded.1; omega,bounded.2⟩

#print axioms HashTableArraysInvariant32.set_call_uniform_bounded
end InitECandidate.Runtime
