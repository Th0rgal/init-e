import InitECandidate.Runtime.HashTableDeleteCallRecordFrameSupported
import InitECandidate.Runtime.JournalSavedValuesIn
import InitECandidate.Runtime.RollbackWorldDeleteSeparated
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual registered deletion preserves the saved-value journal and separated rollback world with a uniform bound. -/
theorem RollbackWorld.registered_delete_saved_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (watched targets : Set (BitVec 64))
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (journalBound : journal.toNat + count.toNat * 32 ≤ 33806089496)
    (journalBefore : journal.toNat + count.toNat * 32 ≤ table.toNat)
    (ticks : 2 ^ 42 ≤ state.clock)
    (tableArgument keyArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      RollbackWorld widths tables journal snapshot count post ∧ RollbackPhysicalSeparated widths tables post ∧
      JournalSavedValuesIn journal count.toNat watched targets post ∧
      state.clock ≤ post.clock + 2 ^ 42 ∧ post.clock ≤ state.clock := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := world.ready table member
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  obtain ⟨post,run,nextWorld,nextSep,cost,remaining⟩ := RollbackWorld.delete_call_preserves_separation state widths tables
    table pointer keys stride capacity used values order reverse items key bits supported ready small large tableArgument keyArgument args aligned words bytes (by omega)
    journal snapshot count world member separated
  obtain ⟨checked,checkedRun,_,frame,_⟩ := ready.delete_call_supported_with_record_frame state (widths table) table pointer keys stride capacity used values order reverse items key bits supported
    tableArgument keyArgument args aligned words bytes (by omega) journal count.toNat journalBound (Or.inr journalBefore)
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  have postSaved : JournalSavedValuesIn journal count.toNat watched targets post := by
    rw [same]
    exact saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; exact frame index inside offset (by simp at belongs ⊢; omega))
  exact ⟨post,run,nextWorld,nextSep,postSaved,by omega,remaining⟩

#print axioms RollbackWorld.registered_delete_saved_values_in
end InitECandidate.Runtime
