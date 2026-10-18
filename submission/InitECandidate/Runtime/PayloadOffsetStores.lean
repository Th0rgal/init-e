import InitECandidate.Runtime.PayloadStoreTailBound
import InitECandidate.Runtime.HashTableReadyJournal32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def payloadOffsetStores : ProgHOL 64 :=
  (.seq (.store (.var .global (ofString "ssz_offs")) (.var .local (ofString "o_extra"))) (.seq (.store (.op .add [.var .global (ofString "ssz_offs"),.const 8]) (.var .local (ofString "o_txs"))) (.seq (.store (.op .add [.var .global (ofString "ssz_offs"),.const 16]) (.var .local (ofString "o_wd"))) (.store (.op .add [.var .global (ofString "ssz_offs"),.const 24]) (.var .local (ofString "o_bal"))))))

theorem source_payload_offset_stores : payloadAt 8 =
  (.seq (.store (.var .global (ofString "ssz_offs")) (.var .local (ofString "o_extra"))) (.seq (.store (.op .add [.var .global (ofString "ssz_offs"),.const 8]) (.var .local (ofString "o_txs"))) (.seq (.store (.op .add [.var .global (ofString "ssz_offs"),.const 16]) (.var .local (ofString "o_wd"))) (.seq (.store (.op .add [.var .global (ofString "ssz_offs"),.const 24]) (.var .local (ofString "o_bal"))) (payloadAt 12))))) := by
  simp only [payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_payload_offset_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (offsets extra txs withdrawals balance : BitVec 64)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (atExtra : state.locals.lookup (ofString "o_extra") = some (.val (.word extra)))
    (atTxs : state.locals.lookup (ofString "o_txs") = some (.val (.word txs)))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (domain0 : state.memaddrs (offsets + 0))
    (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16))
    (domain24 : state.memaddrs (offsets + 24))
    : evaluateHOLFiniteState state payloadOffsetStores =
      (none,journalRecordPost32 state offsets extra txs withdrawals balance) := by
  have step0 := evaluate_store_word (state) (offsets + 0) extra
    (.var .global (ofString "ssz_offs")) (.var .local (ofString "o_extra"))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,atOffsets,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [sourceWriteWord,evalHOLExact,atExtra]) domain0
  have step1 := evaluate_store_word (sourceWriteWord (state) (offsets + 0) extra) (offsets + 8) txs
    (.op .add [.var .global (ofString "ssz_offs"),.const 8]) (.var .local (ofString "o_txs"))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,atOffsets,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [sourceWriteWord,evalHOLExact,atTxs]) domain8
  have step2 := evaluate_store_word (sourceWriteWord (sourceWriteWord (state) (offsets + 0) extra) (offsets + 8) txs) (offsets + 16) withdrawals
    (.op .add [.var .global (ofString "ssz_offs"),.const 16]) (.var .local (ofString "o_wd"))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,atOffsets,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [sourceWriteWord,evalHOLExact,atWithdrawals]) domain16
  have step3 := evaluate_store_word (sourceWriteWord (sourceWriteWord (sourceWriteWord (state) (offsets + 0) extra) (offsets + 8) txs) (offsets + 16) withdrawals) (offsets + 24) balance
    (.op .add [.var .global (ofString "ssz_offs"),.const 24]) (.var .local (ofString "o_bal"))
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,atOffsets,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [sourceWriteWord,evalHOLExact,atBalance]) domain24
  simpa [payloadOffsetStores,journalRecordPost32] using
    (evaluate_seq_none step0 (evaluate_seq_none step1 (evaluate_seq_none step2 step3)))

theorem payload_offset_stores_readback {F : Type} (state : PanSemStateFiniteExact 64 F)
    (offsets extra txs withdrawals balance : BitVec 64) :
    (journalRecordPost32 state offsets extra txs withdrawals balance).memory (offsets + 0) = .word extra ∧
    (journalRecordPost32 state offsets extra txs withdrawals balance).memory (offsets + 8) = .word txs ∧
    (journalRecordPost32 state offsets extra txs withdrawals balance).memory (offsets + 16) = .word withdrawals ∧
    (journalRecordPost32 state offsets extra txs withdrawals balance).memory (offsets + 24) = .word balance := by
  simp [journalRecordPost32,sourceWriteWord]

#print axioms evaluate_payload_offset_stores
#print axioms payload_offset_stores_readback
end InitECandidate.Runtime
