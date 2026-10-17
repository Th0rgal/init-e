import InitECandidate.Runtime.StateRestoreRecordApplicationPreserves
import InitECandidate.Runtime.HashTableReadyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original decrement plus record application has the same clock bound. -/
theorem HashTableReady.restore_iteration_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count snapshot present value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (capacityLarge : 1 < capacity.toNat)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (snapshotLocal : state.locals.lookup (ofString "snap") = some (.val (.word snapshot)))
    (active : 0 < stateRestoreRank state)
    (ticks : 2 ^ 72 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (tableDomain : state.memaddrs (journal + (count - 1) * 32))
    (tableCell : state.memory (journal + (count - 1) * 32) = .word table)
    (keyDomain : state.memaddrs (journal + (count - 1) * 32 + 8))
    (keyCell : state.memory (journal + (count - 1) * 32 + 8) = .word key)
    (presentDomain : state.memaddrs (journal + (count - 1) * 32 + 16)) (presentCell : state.memory (journal + (count - 1) * 32 + 16) = .word present)
    (valueDomain : state.memaddrs (journal + (count - 1) * 32 + 24)) (valueCell : state.memory (journal + (count - 1) * 32 + 24) = .word value)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state stateRestoreLoopBody = (none,post) ∧
      (∃ nextPointer nextKeys nextCapacity nextUsed nextValues nextOrder nextOrderPos nextItems nextBits,
        HashTableReady keyLength table nextKeys stride nextCapacity nextUsed nextValues nextOrder nextOrderPos nextItems nextBits nextPointer post) ∧
      stateRestoreRank post < stateRestoreRank state ∧
      state.clock ≤ post.clock + 2 ^ 72 ∧ post.clock ≤ state.clock := by
  let entry := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count - 1))) state
  have entryReady := ready.after_global state keyLength table pointer keys stride capacity used values order orderPos items bits
    (ofString "journal_n") (.val (.word (count - 1))) (by decide)
  have journalAfter : entry.globals.lookup (ofString "journal") = some (.val (.word journal)) := by
    have distinct : ofString "journal_n" ≠ ofString "journal" := by decide
    simpa [entry,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct] using journalGlobal
  have countAfter : entry.globals.lookup (ofString "journal_n") = some (.val (.word (count - 1))) := by
    simp [entry,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,application,postReady,rank,cost,remaining⟩ := entryReady.restore_record_application_preserves entry keyLength table pointer keys stride capacity used values order orderPos items key journal (count - 1) present value bits supported strideBound capacityLarge safePlan ticks domain
    journalAfter countAfter tableDomain tableCell keyDomain keyCell presentDomain presentCell valueDomain valueCell keyAligned keyWords keyBytes
  have run := evaluate_seq_none (evaluate_stateRestore_decrement state count countGlobal) application
  have decrease := stateRestoreRank_decrement state count snapshot countGlobal snapshotLocal active
  exact ⟨post,stateRestore_loop_body_shape ▸ run,postReady,rank ▸ decrease,cost,remaining⟩

#print axioms HashTableReady.restore_iteration_preserves
end InitECandidate.Runtime
