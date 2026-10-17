import InitECandidate.Runtime.HashTableReadyJournal32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The four original jset stores with their source local expressions. -/
def journalRecordSource32 (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.var .local (ofString "r")) (.var .local (ofString "t")))
    (.seq (.store (.op .add [.var .local (ofString "r"),.const 8]) (.var .local (ofString "kc")))
      (.seq (.store (.op .add [.var .local (ofString "r"),.const 16]) (.rfield 0 (.var .local (ofString "old"))))
        (.seq (.store (.op .add [.var .local (ofString "r"),.const 24]) (.rfield 1 (.var .local (ofString "old")))) continuation)))

theorem evaluate_journalRecordSource32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record table key present value : BitVec 64) (continuation : ProgHOL 64)
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word key)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]))
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (record + BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState state (journalRecordSource32 continuation) =
      evaluateHOLFiniteState (journalRecordPost32 state record table key present value) continuation := by
  have step0 := evaluate_store_word (state) record table (.var .local (ofString "r")) (.var .local (ofString "t"))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (by simpa using domain 0 (by simp))
  have step1 := evaluate_store_word (sourceWriteWord (state) record table) (record + 8) key (.op .add [.var .local (ofString "r"),.const 8]) (.var .local (ofString "kc"))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (domain 8 (by simp))
  have step2 := evaluate_store_word (sourceWriteWord (sourceWriteWord (state) record table) (record + 8) key) (record + 16) present (.op .add [.var .local (ofString "r"),.const 16]) (.rfield 0 (.var .local (ofString "old")))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (domain 16 (by simp))
  have step3 := evaluate_store_word (sourceWriteWord (sourceWriteWord (sourceWriteWord (state) record table) (record + 8) key) (record + 16) present) (record + 24) value (.op .add [.var .local (ofString "r"),.const 24]) (.rfield 1 (.var .local (ofString "old")))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,toExact,r,t,kc,old,wordOpHOL,wordOp,valueIsWord,valueWord]) (domain 24 (by simp))
  unfold journalRecordSource32
  have run := evaluate_seq_none step0 (evaluate_seq_none step1 (evaluate_seq_none step2
    (evaluate_seq_none step3 (rfl : evaluateHOLFiniteState (journalRecordPost32 state record table key present value) continuation = _))))
  exact run

#print axioms evaluate_journalRecordSource32
end InitECandidate.Runtime
