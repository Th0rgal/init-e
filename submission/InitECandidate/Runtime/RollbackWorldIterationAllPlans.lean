import InitECandidate.Runtime.RollbackWorldRecordApplicationAllPlans
import InitECandidate.Runtime.RollbackPhysicalGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual source loop body decrements the live journal prefix, applies the
record and retains both the world and separation with strictly smaller rank. -/
theorem RollbackWorld.iteration_all_plans {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (table pointer keys stride capacity used values order orderPos items key journal count present value : BitVec 64) (bits : Nat)
    (supported : (widths table) = 20 ∨ (widths table) = 32 ∨ (widths table) = 52)
    (ready : HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (capacityLarge : 1 < capacity.toNat)
    (setBudget : 3 * capacity.toNat + 2 * (capacity * 2).toNat + (widths table).toNat + 13 + items.toNat * ((capacity * 2).toNat + (widths table).toNat + 4) ≤ state.clock)
    (deleteBudget : capacity.toNat * 57 + 3 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (tableDomain : state.memaddrs (journal + (count - 1) * 32))
    (tableCell : state.memory (journal + (count - 1) * 32) = .word table)
    (keyDomain : state.memaddrs (journal + (count - 1) * 32 + 8))
    (keyCell : state.memory (journal + (count - 1) * 32 + 8) = .word key)
    (presentDomain : state.memaddrs (journal + (count - 1) * 32 + 16)) (presentCell : state.memory (journal + (count - 1) * 32 + 16) = .word present)
    (valueDomain : state.memaddrs (journal + (count - 1) * 32 + 24)) (valueCell : state.memory (journal + (count - 1) * 32 + 24) = .word value)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (snapshot : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (registered : table ∈ tables)
    (separated : RollbackPhysicalSeparated widths tables state)
    (active : snapshot.toNat < count.toNat) :
    (∃ post, evaluateHOLFiniteState state stateRestoreLoopBody = (none,post) ∧
      RollbackWorld widths tables journal snapshot (count - 1) post ∧ RollbackPhysicalSeparated widths tables post ∧ stateRestoreRank post < stateRestoreRank state) ∨
    ((evaluateHOLFiniteState state stateRestoreLoopBody).1 ≠ none ∧
      (evaluateHOLFiniteState state stateRestoreLoopBody).1 ≠ some .timeOut ∧
      (∀ output : ValueHOL 64, (evaluateHOLFiniteState state stateRestoreLoopBody).1 ≠ some (.returned output)) ∧
      (evaluateHOLFiniteState state stateRestoreLoopBody).1 ≠ some .continue) := by
  let entry := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count - 1))) state
  have entryWorld := world.decrement active
  have entrySeparated := separated.after_global (ofString "journal_n") (.val (.word (count - 1))) (by decide)
  have entryReady := ready.after_global state (widths table) table pointer keys stride capacity used values order orderPos items bits
    (ofString "journal_n") (.val (.word (count - 1))) (by decide)
  have outcome := RollbackWorld.record_application_all_plans entry widths tables
    table pointer keys stride capacity used values order orderPos items key journal (count - 1) present value bits supported entryReady
    strideBound capacityLarge setBudget deleteBudget domain entryWorld.journalGlobal entryWorld.counter
    tableDomain tableCell keyDomain keyCell presentDomain presentCell valueDomain valueCell keyAligned keyWords keyBytes
    snapshot entryWorld registered entrySeparated
  rcases outcome with success | failure
  · obtain ⟨post,application,postWorld,postSeparated⟩ := success
    have run := evaluate_seq_none (evaluate_stateRestore_decrement state count world.counter) application
    have beforeRank := stateRestoreRank_of_bindings state count snapshot world.counter world.snapshotLocal
    have afterRank := stateRestoreRank_of_bindings post (count - 1) snapshot postWorld.counter postWorld.snapshotLocal
    have decrease := (stateRestore_rank_decreases count snapshot active).2
    exact Or.inl ⟨post,stateRestore_loop_body_shape ▸ run,postWorld,postSeparated,by omega⟩
  · have run := evaluate_seq_none (evaluate_stateRestore_decrement state count world.counter)
      (show evaluateHOLFiniteState (setKvarHOLFinite .global (ofString "journal_n") (.val (.word (count - 1))) state) stateRestoreApplyRecord = evaluateHOLFiniteState entry stateRestoreApplyRecord from rfl)
    rw [stateRestore_loop_body_shape,run]
    exact Or.inr failure

#print axioms RollbackWorld.iteration_all_plans
end InitECandidate.Runtime
