import InitECandidate.Runtime.JournalDeleteSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual deletion journal stores save a constant presence flag of one. -/
theorem evaluate_journalDeleteRecordSource32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record table key present value : BitVec 64) (continuation : ProgHOL 64)
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word key)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]))
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (record + BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState state (journalDeleteRecordSource32 continuation) =
      evaluateHOLFiniteState (journalRecordPost32 state record table key 1 value) continuation := by
  have step0 := evaluate_store_word (state) record table (.var .local (ofString "r")) (.var .local (ofString "t"))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (by simpa using domain 0 (by simp))
  have step1 := evaluate_store_word (sourceWriteWord (state) record table) (record + 8) key (.op .add [.var .local (ofString "r"),.const 8]) (.var .local (ofString "kc"))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (domain 8 (by simp))
  have step2 := evaluate_store_word (sourceWriteWord (sourceWriteWord (state) record table) (record + 8) key) (record + 16) 1 (.op .add [.var .local (ofString "r"),.const 16]) (.const 1)
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (domain 16 (by simp))
  have step3 := evaluate_store_word (sourceWriteWord (sourceWriteWord (sourceWriteWord (state) record table) (record + 8) key) (record + 16) 1) (record + 24) value (.op .add [.var .local (ofString "r"),.const 24]) (.rfield 1 (.var .local (ofString "old")))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (domain 24 (by simp))
  unfold journalDeleteRecordSource32
  have run := evaluate_seq_none step0 (evaluate_seq_none step1 (evaluate_seq_none step2
    (evaluate_seq_none step3 (rfl : evaluateHOLFiniteState (journalRecordPost32 state record table key 1 value) continuation = _))))
  exact run

#print axioms evaluate_journalDeleteRecordSource32
end InitECandidate.Runtime
