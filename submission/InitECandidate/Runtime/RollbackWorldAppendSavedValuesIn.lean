import InitECandidate.Runtime.JournalSavedValuesAppend
import InitECandidate.Runtime.RollbackWorldAppend
import InitECandidate.Runtime.JournalRecordSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execute the original four local-expression stores and global increment.
Any continuation starts in the enlarged world with no source-clock cost. -/
theorem RollbackWorld.evaluate_record_append_saved_values_in {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (table key present value : BitVec 64) (member : table ∈ tables)
    (watched targets : Set (BitVec 64))
    (savedValues : JournalSavedValuesIn journal count.toNat watched targets state)
    (registered : table ∈ watched → present ≠ 0 → value ∈ targets)
    (space : count.toNat < 524288)
    (address : (journal + BitVec.ofNat 64 count.toNat * 32).toNat = journal.toNat + count.toNat * 32)
    (bounded : (journal + BitVec.ofNat 64 count.toNat * 32).toNat + 32 ≤ 33806089496)
    (headers : ∀ other ∈ tables, (journal + BitVec.ofNat 64 count.toNat * 32).toNat + 32 ≤ other.toNat)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (fields : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (journal + BitVec.ofNat 64 count.toNat * 32 + BitVec.ofNat 64 offset))
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (r : state.locals.lookup (ofString "r") = some (.val (.word (journal + BitVec.ofNat 64 count.toNat * 32))))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word key)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)])) :
    ∃ post, (∀ continuation, evaluateHOLFiniteState state
      (journalRecordSource32 (.seq (.assign .global (ofString "journal_n")
        (.op .add [.var .global (ofString "journal_n"),.const 1])) continuation)) =
      evaluateHOLFiniteState post continuation) ∧
      RollbackWorld widths tables journal snapshot (count + 1) post ∧
      RollbackPhysicalSeparated widths tables post ∧ JournalSavedValuesIn journal (count + 1).toNat watched targets post ∧ post.clock = state.clock ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.code = state.code ∧
      (∀ name, name ≠ ofString "journal_n" → post.globals.lookup name = state.globals.lookup name) := by
  let saved := journalRecordPost32 state (journal + BitVec.ofNat 64 count.toNat * 32) table key present value
  let post := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count + 1))) saved
  obtain ⟨nextWorld,nextSeparated,clock⟩ := world.append_record separated table key present value member space address bounded headers supported fields aligned words bytes
  have frame := journalRecordPost32_prefix_frame state journal (journal + BitVec.ofNat 64 count.toNat * 32) table key present value count.toNat (by omega) bounded (by omega)
  obtain ⟨tableCell,_,presentCell,valueCell⟩ := journalRecordPost32_fields state (journal + BitVec.ofNat 64 count.toNat * 32) table key present value
  have savedValid : JournalSavedValuesIn journal (count.toNat + 1) watched targets saved :=
    savedValues.append (after := saved) (by intro index inside offset belongs; exact frame index inside offset (by simp at belongs ⊢; omega))
      table present value tableCell presentCell valueCell registered
  have nextCount : (count + (1 : BitVec 64)).toNat = count.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by change count.toNat + 1 < 2 ^ 64; omega)]
    rfl
  have postSaved : JournalSavedValuesIn journal (count + 1).toNat watched targets post := by
    rw [nextCount]
    exact savedValid.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)
  refine ⟨post,?_,nextWorld,nextSeparated,postSaved,clock,rfl,rfl,rfl,?_⟩
  · intro continuation
    rw [evaluate_journalRecordSource32 state _ table key present value _ r t kc old fields]
    have counter : saved.globals.lookup (ofString "journal_n") = some (.val (.word count)) := world.counter
    have increment : evaluateHOLFiniteState saved (.assign .global (ofString "journal_n")
        (.op .add [.var .global (ofString "journal_n"),.const 1])) = (none,post) := by
      simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,counter,wordOpHOL,wordOp,valueIsWord,valueWord,
        isValidValueHOLExact,lookupKvarHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,post]
    change evaluateHOLFiniteState saved (.seq _ continuation) = _
    rw [evaluateHOLFiniteState_seq_line780,increment]
  · intro name different
    simp [post,saved,journalRecordPost32,sourceWriteWord,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms RollbackWorld.evaluate_record_append_saved_values_in
end InitECandidate.Runtime
