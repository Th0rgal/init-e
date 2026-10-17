import InitECandidate.Runtime.RollbackPhysicalSeparated
import InitECandidate.Runtime.HashTablePhysicalStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every live region starts at or above its table header, including relocation. -/
theorem rollback_footprint_above_header {F : Type} {widths : BitVec 64 → BitVec 64}
    {table address : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (inside : rollbackTableFootprint widths table state address) : table.toNat ≤ address.toNat := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,region⟩ := inside
  have hk := ready.live.arrays.headerKeys
  have hv := ready.live.arrays.headerValues
  have ku := ready.live.arrays.keysBefore
  have uo := ready.live.arrays.usedBefore
  have oo := ready.live.arrays.orderBefore
  unfold tablePhysicalRegion at region
  omega

/-- Stores outside all live regions retain the registry and its separation. -/
theorem rollback_registry_after_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (address value : BitVec 64)
    (family : ∀ table ∈ tables, RollbackTableReady widths table state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (outside : ∀ table ∈ tables, ¬rollbackTableFootprint widths table state address) :
    (∀ table ∈ tables, RollbackTableReady widths table (sourceWriteWord state address value)) ∧
    RollbackPhysicalSeparated widths tables (sourceWriteWord state address value) := by
  have retained : ∀ table ∈ tables, ∀ pointer keys stride capacity used values order orderPos items bits,
      HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state →
      HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer (sourceWriteWord state address value) := by
    intro table member pointer keys stride capacity used values order orderPos items bits ready
    apply ready.after_word_physical state (widths table) table pointer keys stride capacity used values order orderPos items address value bits
    intro inside
    exact outside table member ((ready.rollback_footprint_iff state widths table pointer keys stride capacity used values order orderPos items bits address).mpr inside)
  constructor
  · intro table member
    obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,small,big⟩ := family table member
    exact ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,retained table member pointer keys stride capacity used values order orderPos items bits ready,small,big⟩
  · apply separated.of_footprint_subset
    intro table member watched inside
    obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,_,_⟩ := family table member
    have updated := retained table member pointer keys stride capacity used values order orderPos items bits ready
    exact (ready.rollback_footprint_iff state widths table pointer keys stride capacity used values order orderPos items bits watched).mpr
      ((updated.rollback_footprint_iff (sourceWriteWord state address value) widths table pointer keys stride capacity used values order orderPos items bits watched).mp inside)

#print axioms rollback_footprint_above_header
#print axioms rollback_registry_after_word
end InitECandidate.Runtime
