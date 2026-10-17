import InitECandidate.Runtime.RollbackWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Retaining the actual record cells preserves their table identities as well
as their typed key extents. Ready-table preservation is supplied separately. -/
theorem RollbackWorld.after_frame {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count next : BitVec 64} {before after : PanSemStateFiniteExact 64 F}
    (valid : RollbackWorld widths tables journal snapshot count before)
    (bound : next.toNat ≤ count.toNat)
    (counter : after.globals.lookup (ofString "journal_n") = some (.val (.word next)))
    (snapshotLocal : after.locals.lookup (ofString "snap") = some (.val (.word snapshot)))
    (journalGlobal : after.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (domain : after.memaddrs = before.memaddrs)
    (frame : ∀ index : Nat, index < next.toNat → ∀ offset ∈ ([0,8,16,24] : List Nat),
      after.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        before.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset))
    (family : ∀ table ∈ tables, RollbackTableReady widths table after) :
    RollbackWorld widths tables journal snapshot next after := by
  refine ⟨counter,snapshotLocal,journalGlobal,by have := valid.capacity; omega,
    valid.records.after_frame bound domain frame,?_,family,?_⟩
  · intro index inside table cell
    have retained := frame index inside 0 (by simp)
    have oldCell : before.memory (journal + BitVec.ofNat 64 index * 32) = .word table := by
      simpa using retained.symm.trans (by simpa using cell)
    exact valid.references index (by omega) table oldCell
  · intro table member
    have oldLayout := valid.layout table member
    omega

/-- The original counter assignment retains the complete world while shrinking
its live record prefix by one. A true guard excludes word underflow. -/
theorem RollbackWorld.decrement {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (valid : RollbackWorld widths tables journal snapshot count state)
    (guard : snapshot.toNat < count.toNat) :
    RollbackWorld widths tables journal snapshot (count - 1)
      (setGlobalHOLFinite (ofString "journal_n") (.val (.word (count - 1))) state) := by
  let entry := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count - 1))) state
  have numeric := (stateRestore_rank_decreases count snapshot guard).1
  apply valid.after_frame (after := entry) (by omega)
  · simp [entry,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact valid.snapshotLocal
  · have distinct : ofString "journal_n" ≠ ofString "journal" := by decide
    simpa [entry,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct] using valid.journalGlobal
  · rfl
  · intro index inside offset member
    rfl
  · intro table member
    obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,strideBound,large⟩ := valid.ready table member
    exact ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,
      ready.after_global state (widths table) table pointer keys stride capacity used values order orderPos items bits
        (ofString "journal_n") (.val (.word (count - 1))) (by decide),strideBound,large⟩

/-- Concrete execution of the source decrement produces the smaller world. -/
theorem RollbackWorld.evaluate_decrement {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (valid : RollbackWorld widths tables journal snapshot count state)
    (guard : snapshot.toNat < count.toNat) :
    ∃ post, evaluateHOLFiniteState state stateRestoreDecrement = (none,post) ∧
      RollbackWorld widths tables journal snapshot (count - 1) post ∧
      post.clock = state.clock := by
  exact ⟨_,evaluate_stateRestore_decrement state count valid.counter,valid.decrement guard,rfl⟩

#print axioms RollbackWorld.after_frame
#print axioms RollbackWorld.decrement
#print axioms RollbackWorld.evaluate_decrement
end InitECandidate.Runtime
