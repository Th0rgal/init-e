import InitECandidate.Runtime.HashTableValuesInJournalRecord
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual record-and-counter prefix of jset preserves registered values. -/
theorem evaluate_journalRecordAppend_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count record savedTable savedKey present savedValue : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (before : record.toNat + 32 ≤ table.toNat)
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word savedTable)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word savedKey)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word savedValue)]))
    (journalCount : BitVec 64)
    (counter : state.globals.lookup (ofString "journal_n") = some (.val (.word journalCount)))
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (record + BitVec.ofNat 64 offset)) :
    ∃ post : PanSemStateFiniteExact 64 F,
      (∀ continuation, evaluateHOLFiniteState state (journalRecordSource32 (.seq (.assign .global (ofString "journal_n")
        (.op .add [.var .global (ofString "journal_n"),.const 1])) continuation)) = evaluateHOLFiniteState post continuation) ∧
      HashTableValuesIn table targets post ∧ post.clock = state.clock ∧ post.locals = state.locals ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (journalCount + 1))) ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let saved := journalRecordPost32 state record savedTable savedKey present savedValue
  let post := setGlobalHOLFinite (ofString "journal_n") (.val (.word (journalCount + 1))) saved
  have savedRegistered := entries.journal_record_before state keyLength table keys stride capacity used values order orderPos count record savedTable savedKey present savedValue bits arrays targets before
  have increment : evaluateHOLFiniteState saved (.assign .global (ofString "journal_n")
      (.op .add [.var .global (ofString "journal_n"),.const 1])) = (none,post) := by
    have savedCounter : saved.globals.lookup (ofString "journal_n") = some (.val (.word journalCount)) := counter
    simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,savedCounter,wordOpHOL,wordOp,valueIsWord,valueWord,
      isValidValueHOLExact,lookupKvarHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,post]
  refine ⟨post,?_,savedRegistered.after_read rfl rfl rfl,rfl,rfl,?_,rfl,rfl,rfl⟩
  · intro continuation
    rw [evaluate_journalRecordSource32 state record savedTable savedKey present savedValue _ r t kc old domain]
    change evaluateHOLFiniteState saved (.seq _ continuation) = _
    rw [evaluateHOLFiniteState_seq_line780,increment]
  · simp [post,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms evaluate_journalRecordAppend_values_in
end InitECandidate.Runtime
