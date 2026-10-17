import InitECandidate.Runtime.HashTablePhysicalAdvanceFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The stored header uniquely determines the live physical regions. Different
proof witnesses for counts, ranks or frontiers cannot change that footprint. -/
theorem HashTableReady.physical_region_eq {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (otherKeyLength otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (other : HashTableReady otherKeyLength table otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state) :
    tablePhysicalRegion table keys stride capacity used values order orderPos =
      tablePhysicalRegion table otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos := by
  have strideEq : stride = otherStride := by
    simpa only [HolWordLab.word.injEq] using ready.live.arrays.cell8.symm.trans other.live.arrays.cell8
  have capacityEq : capacity = otherCapacity := by
    simpa only [HolWordLab.word.injEq] using ready.live.arrays.cell16.symm.trans other.live.arrays.cell16
  have keysEq : keys = otherKeys := by
    simpa only [HolWordLab.word.injEq] using ready.live.arrays.cell32.symm.trans other.live.arrays.cell32
  have valuesEq : values = otherValues := by
    simpa only [HolWordLab.word.injEq] using ready.live.arrays.cell40.symm.trans other.live.arrays.cell40
  have usedEq : used = otherUsed := by
    simpa only [HolWordLab.word.injEq] using ready.live.arrays.cell48.symm.trans other.live.arrays.cell48
  have orderEq : order = otherOrder := by
    simpa only [HolWordLab.word.injEq] using ready.live.arrays.cell56.symm.trans other.live.arrays.cell56
  have orderPosEq : orderPos = otherOrderPos := by
    simpa only [HolWordLab.word.injEq] using ready.live.arrays.cell64.symm.trans other.live.arrays.cell64
  rw [strideEq,capacityEq,keysEq,valuesEq,usedEq,orderEq,orderPosEq]

/-- Relocated arrays start at the old shared frontier. They remain disjoint
from every old live region; only the unchanged header needs an explicit frame. -/
theorem HashTableReady.relocated_physical_separate {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table pointer stride capacity used values order orderPos items keyLength next : BitVec 64) (bits : Nat)
    (grown : HashTableReady keyLength table pointer stride capacity used values order orderPos items bits next post)
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (other : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (header : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < table.toNat + 72 →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∀ address : BitVec 64, tablePhysicalRegion table pointer stride capacity used values order orderPos address →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address := by
  intro address member otherMember
  have below := other.physical_below_frontier state otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits address otherMember
  have ku := grown.live.arrays.keysBefore
  have uo := grown.live.arrays.usedBefore
  have oo := grown.live.arrays.orderBefore
  have kv := grown.ordering
  rcases member with inHeader | inArrays
  · exact header address inHeader.1 inHeader.2 otherMember
  · omega

#print axioms HashTableReady.physical_region_eq
#print axioms HashTableReady.relocated_physical_separate
end InitECandidate.Runtime
