import InitECandidate.Runtime.JournalUndoRecordIntervals
import InitECandidate.Runtime.HashTableReadyInsertSupported
import InitECandidate.Runtime.HashTableOutsideHeaderRegionSupported
import InitECandidate.Runtime.HashTableReadyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual insertion preserves an earlier allocated table even when it lies
between the target header and the target's relocated arrays. -/
theorem HashTableReady.insert_supported_with_journal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + keyLength.toNat + 3 ≤ state.clock)
    (journal : BitVec 64) (journalCount : Nat)
    (otherReady : JournalUndoRecords journal journalCount state)
    (journalBound : journal.toNat + journalCount * 32 ≤ 33806089496)
    (beforeKeys : journal.toNat + journalCount * 32 ≤ keys.toNat)
    (beforeValues : journal.toNat + journalCount * 32 ≤ values.toNat)
    (separateHeader : journal.toNat + journalCount * 32 ≤ table.toNat ∨
      table.toNat + 72 ≤ journal.toNat) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos (count + 1) bits pointer post ∧
      JournalUndoRecords journal journalCount post ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧
      post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,valid,cost,remaining,locals,globals,domain,endian⟩ :=
    ready.insert_supported state keyLength table pointer keys stride capacity used values order orderPos count key value bits supported
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
  obtain ⟨checked,checkedRun,_,_,_,_,_,_,_,frame⟩ :=
    ready.live.arrays.insert_supported_preserves_outside_header state keyLength table keys stride capacity used values order orderPos count key value bits
      (journal.toNat + journalCount * 32) supported beforeKeys beforeValues
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  have code : post.code = state.code := valid.live.arrays.code.trans ready.live.arrays.code.symm
  have otherValid : JournalUndoRecords journal journalCount post := by
    apply otherReady.after_frame (after := post) (Nat.le_refl _) domain
    intro index inside offset member
    have smallOffset : offset < 32 := by simp at member; omega
    have interval := journal_undo_field_interval journal journalCount index offset journalBound inside smallOffset
    rw [same]
    apply frame _ _ interval.2
    rcases separateHeader with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  exact ⟨post,run,valid,otherValid,cost,remaining,locals,globals,domain,endian⟩

#print axioms HashTableReady.insert_supported_with_journal
end InitECandidate.Runtime
