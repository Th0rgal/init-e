import InitECandidate.Runtime.HashGrowTwoPhysicalTablesSupported
import InitECandidate.Runtime.HashTableGrowOldArraysWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A reusable two-table growth contract deriving old-array and heap facts
from the target invariant rather than requiring them at every caller. -/
theorem HashTableReady.grow_supported_with_physical_table {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (tableArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument] = some [.val (.word table)])
    (strideBound : stride.toNat ≤ 56)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separate : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < table.toNat + 72 →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [tableArgument]) = (none,post) ∧
      HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) items (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      state.clock ≤ post.clock + (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have old := ready.live.arrays.old_arrays_width state keyLength table keys stride capacity used values order orderPos items bits pointer.toNat
    ready.live.entries ready.live.frontier.allocated (by have bound := ready.live.frontier.bounded; omega)
  have header : table.toNat + 72 ≤ pointer.toNat := by
    have before := old.headerOrder
    have allocated := old.orderEnd
    omega
  exact evaluate_htabGrow_supported_two_physical_tables state keyLength table pointer capacity stride keys values order items bits supported tableArgument arguments
    ready.live.arrays.code ready.live.arrays.power old ready.live.arrays.strideAligned ready.live.arrays.fits strideBound
    ready.live.frontier.aligned header ready.live.frontier.bounded
    (by have u := ready.live.arrays.usedBefore; have o := ready.live.arrays.orderBefore; have e := ready.live.arrays.endBound; omega)
    safePlan ticks ready.live.frontier.heap domain ready.live.arrays.cell0 ready.live.arrays.cell16 ready.live.arrays.cell8
    ready.live.arrays.cell32 ready.live.arrays.cell40 ready.live.arrays.cell56 ready.live.arrays.cell24
    otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady separate

#print axioms HashTableReady.grow_supported_with_physical_table
end InitECandidate.Runtime
