import InitECandidate.Runtime.HashTablePhysicalIdentity
import InitECandidate.Runtime.RollbackWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The live footprint read from any valid description of this table. Header
uniqueness makes this independent of existential invariant witnesses. -/
def rollbackTableFootprint {F : Type} (widths : BitVec 64 → BitVec 64) (table : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) (address : BitVec 64) : Prop :=
  ∃ pointer keys stride capacity used values order orderPos items : BitVec 64, ∃ bits : Nat,
    HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state ∧
    tablePhysicalRegion table keys stride capacity used values order orderPos address

def RollbackPhysicalSeparated {F : Type} (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ table ∈ tables, ∀ other ∈ tables, table ≠ other → ∀ address,
    rollbackTableFootprint widths table state address → ¬rollbackTableFootprint widths other state address

theorem HashTableReady.rollback_footprint_iff {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state)
    (address : BitVec 64) :
    rollbackTableFootprint widths table state address ↔ tablePhysicalRegion table keys stride capacity used values order orderPos address := by
  constructor
  · rintro ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,other,member⟩
    have equal := ready.physical_region_eq state (widths table) table pointer keys stride capacity used values order orderPos items bits
      (widths table) op ok os oc ou ov oo oop oi ob other
    rw [equal]
    exact member
  · intro member
    exact ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,member⟩

theorem RollbackPhysicalSeparated.of_footprint_subset {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {before after : PanSemStateFiniteExact 64 F}
    (separated : RollbackPhysicalSeparated widths tables before)
    (subset : ∀ table ∈ tables, ∀ address, rollbackTableFootprint widths table after address → rollbackTableFootprint widths table before address) :
    RollbackPhysicalSeparated widths tables after := by
  intro table member other otherMember different address inside otherInside
  exact separated table member other otherMember different address (subset table member address inside) (subset other otherMember address otherInside)

#print axioms HashTableReady.rollback_footprint_iff
#print axioms RollbackPhysicalSeparated.of_footprint_subset
end InitECandidate.Runtime
