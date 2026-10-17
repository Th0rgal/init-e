import InitECandidate.Runtime.TypedJournalUndoRecords
import InitECandidate.Runtime.HashTableReadyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Table facts used by rollback. A fixed table identity keeps its key width,
while all array pointers, occupancy and heap frontier may change. -/
def RollbackTableReady {F : Type} (widths : BitVec 64 → BitVec 64) (table : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ pointer keys stride capacity used values order orderPos items : BitVec 64, ∃ bits : Nat,
    HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state ∧
    stride.toNat ≤ 56 ∧ 1 < capacity.toNat

/-- Concrete entry facts for the original rollback loop. Safe allocation and
preservation of the entire registered-table family remain separate obligations. -/
structure RollbackWorld {F : Type} (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Prop where
  counter : state.globals.lookup (ofString "journal_n") = some (.val (.word count))
  snapshotLocal : state.locals.lookup (ofString "snap") = some (.val (.word snapshot))
  journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal))
  capacity : count.toNat ≤ 524288
  records : TypedJournalUndoRecords widths journal count.toNat state
  references : ∀ index : Nat, index < count.toNat → ∀ table : BitVec 64,
    state.memory (journal + BitVec.ofNat 64 index * 32) = .word table → table ∈ tables
  ready : ∀ table ∈ tables, RollbackTableReady widths table state
  layout : ∀ table ∈ tables, journal.toNat + count.toNat * 32 ≤ table.toNat

theorem RollbackTableReady.after_read {F : Type} {widths : BitVec 64 → BitVec 64} {table : BitVec 64}
    {before after : PanSemStateFiniteExact 64 F} (valid : RollbackTableReady widths table before)
    (memory : after.memory = before.memory) (globals : after.globals = before.globals)
    (code : after.code = before.code) (domain : after.memaddrs = before.memaddrs) (endian : after.be = before.be) :
    RollbackTableReady widths table after := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,strideBound,large⟩ := valid
  exact ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,
    ready.after_read before after (widths table) table keys stride capacity used values order orderPos items bits pointer memory globals code domain endian,strideBound,large⟩

theorem RollbackWorld.dec_clock {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (valid : RollbackWorld widths tables journal snapshot count state) :
    RollbackWorld widths tables journal snapshot count (decClockHOLFinite state) := by
  exact { valid with
    records := valid.records.after_frame (after := decClockHOLFinite state) (Nat.le_refl _) rfl (by intro index inside offset member; rfl)
    ready := fun table member => (valid.ready table member).after_read rfl rfl rfl rfl rfl }

/-- The next actual journal record refers to a live table and carries the key
extent assigned to that same table, not an unrelated supported width. -/
theorem RollbackWorld.select_last {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (valid : RollbackWorld widths tables journal snapshot count state) (active : 0 < stateRestoreRank state) :
    ∃ table key present value : BitVec 64,
      RollbackTableReady widths table state ∧
      (widths table = 20 ∨ widths table = 32 ∨ widths table = 52) ∧
      state.memory (journal + (count - 1) * 32) = .word table ∧
      state.memory (journal + (count - 1) * 32 + 8) = .word key ∧
      state.memory (journal + (count - 1) * 32 + 16) = .word present ∧
      state.memory (journal + (count - 1) * 32 + 24) = .word value ∧
      key.toNat % 8 = 0 ∧
      (∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset)) ∧
      (∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) := by
  have rank := stateRestoreRank_of_bindings state count snapshot valid.counter valid.snapshotLocal
  have numeric := (stateRestore_rank_decreases count snapshot (by omega)).1
  have inside : (count - 1).toNat < count.toNat := by omega
  obtain ⟨table,key,present,value,supported,t,k,p,v,aligned,words,bytes⟩ := valid.records.select inside
  have member := valid.references (count - 1).toNat inside table t
  have indexWord : BitVec.ofNat 64 (count - 1).toNat = count - 1 := by
    apply BitVec.eq_of_toNat_eq
    change (count - 1).toNat % 2 ^ 64 = (count - 1).toNat
    exact Nat.mod_eq_of_lt (count - 1).isLt
  simpa only [indexWord] using (show ∃ table key present value : BitVec 64,
    RollbackTableReady widths table state ∧ (widths table = 20 ∨ widths table = 32 ∨ widths table = 52) ∧
    state.memory (journal + BitVec.ofNat 64 (count - 1).toNat * 32) = .word table ∧
    state.memory (journal + BitVec.ofNat 64 (count - 1).toNat * 32 + 8) = .word key ∧
    state.memory (journal + BitVec.ofNat 64 (count - 1).toNat * 32 + 16) = .word present ∧
    state.memory (journal + BitVec.ofNat 64 (count - 1).toNat * 32 + 24) = .word value ∧
    key.toNat % 8 = 0 ∧
    (∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset)) ∧
    (∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) from
      ⟨table,key,present,value,valid.ready table member,supported,t,k,p,v,aligned,words,bytes⟩)

#print axioms RollbackTableReady.after_read
#print axioms RollbackWorld.dec_clock
#print axioms RollbackWorld.select_last
end InitECandidate.Runtime
