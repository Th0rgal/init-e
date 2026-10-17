import InitECandidate.Runtime.RollbackWorldFrame
import InitECandidate.Runtime.RollbackPhysicalSeparated
import InitECandidate.Runtime.JournalUndoRecordIntervals
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An update confined to one unchanged table layout preserves the full world
and physical separation, independently of any prospective allocation plan. -/
theorem RollbackWorld.after_physical_update {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state post : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (table pointer keys stride capacity used values order orderPos items nextItems : BitVec 64) (bits : Nat)
    (registered : table ∈ tables)
    (ready : HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state)
    (updated : HashTableReady (widths table) table keys stride capacity used values order orderPos nextItems bits pointer post)
    (strideBound : stride.toNat ≤ 56) (large : 1 < capacity.toNat)
    (frame : ∀ address : BitVec 64, ¬tablePhysicalRegion table keys stride capacity used values order orderPos address → post.memory address = state.memory address)
    (locals : post.locals = state.locals) (globals : post.globals = state.globals)
    (code : post.code = state.code) (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    RollbackWorld widths tables journal snapshot count post ∧ RollbackPhysicalSeparated widths tables post := by
  have otherReady : ∀ other ∈ tables, other ≠ table → ∀ op ok os oc ou ov oo oop oi ob,
      HashTableReady (widths other) other ok os oc ou ov oo oop oi ob op state →
      HashTableReady (widths other) other ok os oc ou ov oo oop oi ob op post := by
    intro other member different op ok os oc ou ov oo oop oi ob valid
    apply valid.physical_frame state post (widths other) other op ok os oc ou ov oo oop oi ob
      ?_ globals code domain endian
    intro address inside
    apply frame address
    intro targetMember
    exact separated table registered other member (Ne.symm different) address
      ((ready.rollback_footprint_iff state widths table pointer keys stride capacity used values order orderPos items bits address).mpr targetMember)
      ((valid.rollback_footprint_iff state widths other op ok os oc ou ov oo oop oi ob address).mpr inside)
  have family : ∀ other ∈ tables, RollbackTableReady widths other post := by
    intro other member
    by_cases same : other = table
    · subst other
      exact ⟨pointer,keys,stride,capacity,used,values,order,orderPos,nextItems,bits,updated,strideBound,large⟩
    · obtain ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,valid,small,big⟩ := world.ready other member
      exact ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,otherReady other member same op ok os oc ou ov oo oop oi ob valid,small,big⟩
  have subset : ∀ other ∈ tables, ∀ address, rollbackTableFootprint widths other post address → rollbackTableFootprint widths other state address := by
    intro other member address inside
    by_cases same : other = table
    · subst other
      exact (ready.rollback_footprint_iff state widths table pointer keys stride capacity used values order orderPos items bits address).mpr
        ((updated.rollback_footprint_iff post widths table pointer keys stride capacity used values order orderPos nextItems bits address).mp inside)
    · obtain ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,valid,_,_⟩ := world.ready other member
      have retained := otherReady other member same op ok os oc ou ov oo oop oi ob valid
      exact (valid.rollback_footprint_iff state widths other op ok os oc ou ov oo oop oi ob address).mpr
        ((retained.rollback_footprint_iff post widths other op ok os oc ou ov oo oop oi ob address).mp inside)
  have before := world.layout table registered
  have hk := ready.live.arrays.headerKeys
  have hv := ready.live.arrays.headerValues
  have ku := ready.live.arrays.keysBefore
  have vu := ready.live.arrays.valuesBefore
  have uo := ready.live.arrays.usedBefore
  have oo := ready.live.arrays.orderBefore
  have bounded := ready.live.arrays.endBound
  have journalBound : journal.toNat + count.toNat * 32 ≤ 33806089496 := by omega
  have records : ∀ index : Nat, index < count.toNat → ∀ offset ∈ ([0,8,16,24] : List Nat),
      post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) := by
    intro index inside offset member
    have small : offset < 32 := by simp at member; omega
    have interval := journal_undo_field_interval journal count.toNat index offset journalBound inside small
    apply frame
    unfold tablePhysicalRegion
    omega
  exact ⟨world.after_frame (Nat.le_refl _) (by rw [globals]; exact world.counter)
    (by rw [locals]; exact world.snapshotLocal) (by rw [globals]; exact world.journalGlobal) domain records family,
    separated.of_footprint_subset subset⟩

#print axioms RollbackWorld.after_physical_update
end InitECandidate.Runtime
