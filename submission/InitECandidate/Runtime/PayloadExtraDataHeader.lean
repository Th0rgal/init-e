import InitECandidate.Runtime.PayloadExtraDataGuard
import InitECandidate.Runtime.FrameHalt
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def payloadExtraDataHeader : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "pl"),.const 16])
      (.op .add [.var .local (ofString "p"),.var .local (ofString "o_extra")]))
    (.store (.op .add [.var .local (ofString "pl"),.const 24])
      (.op .sub [.var .local (ofString "o_txs"),.var .local (ofString "o_extra")]))

noncomputable def payloadExtraDataHeaderPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload pointer extra transactions : BitVec 64) : PanSemStateFiniteExact 64 F :=
  sourceWriteWord (sourceWriteWord state (payload + 16) (pointer + extra)) (payload + 24) (transactions - extra)

theorem evaluate_payload_extra_data_header_source {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state (payloadAt 14) =
      evaluateHOLFiniteState state (.seq payloadExtraDataHeader (payloadAt 16)) := by
  have source : payloadAt 14 =
      .seq (.store (.op .add [.var .local (ofString "pl"),.const 16])
        (.op .add [.var .local (ofString "p"),.var .local (ofString "o_extra")]))
      (.seq (.store (.op .add [.var .local (ofString "pl"),.const 24])
        (.op .sub [.var .local (ofString "o_txs"),.var .local (ofString "o_extra")])) (payloadAt 16)) := by
    simp only [payloadAt,authorizationNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  rw [source,← evaluate_seq_assoc]
  rfl

theorem evaluate_payload_extra_data_header_writes {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload pointer extra transactions : BitVec 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atExtra : state.locals.lookup (ofString "o_extra") = some (.val (.word extra)))
    (atTransactions : state.locals.lookup (ofString "o_txs") = some (.val (.word transactions)))
    (pointerDomain : state.memaddrs (payload + 16)) (lengthDomain : state.memaddrs (payload + 24)) :
    evaluateHOLFiniteState state payloadExtraDataHeader =
      (none,payloadExtraDataHeaderPost state payload pointer extra transactions) := by
  have one := evaluate_store_word state (payload + 16) (pointer + extra)
    (.op .add [.var .local (ofString "pl"),.const 16])
    (.op .add [.var .local (ofString "p"),.var .local (ofString "o_extra")])
    (by simp [evalHOLExact,evalListHOLExact,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,evalListHOLExact,atPointer,atExtra,wordOpHOL,wordOp,valueIsWord,valueWord]) pointerDomain
  have two := evaluate_store_word (sourceWriteWord state (payload + 16) (pointer + extra)) (payload + 24) (transactions - extra)
    (.op .add [.var .local (ofString "pl"),.const 24])
    (.op .sub [.var .local (ofString "o_txs"),.var .local (ofString "o_extra")])
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [sourceWriteWord,evalHOLExact,evalListHOLExact,atTransactions,atExtra,wordOpHOL,wordOp,valueIsWord,valueWord]) lengthDomain
  exact evaluate_seq_none one two

theorem payload_extra_data_header_readback {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload pointer extra transactions : BitVec 64) :
    (payloadExtraDataHeaderPost state payload pointer extra transactions).memory (payload + 16) = .word (pointer + extra) ∧
    (payloadExtraDataHeaderPost state payload pointer extra transactions).memory (payload + 24) = .word (transactions - extra) := by
  simp [payloadExtraDataHeaderPost,sourceWriteWord]

/-- The final header prefix transfers control to the actual transaction-list
call with unchanged locals, globals and clock, after recording extra data. -/
theorem payload_extra_data_header_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload pointer extra transactions : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atExtra : state.locals.lookup (ofString "o_extra") = some (.val (.word extra)))
    (atTransactions : state.locals.lookup (ofString "o_txs") = some (.val (.word transactions)))
    (pointerDomain : state.memaddrs (payload + 16)) (lengthDomain : state.memaddrs (payload + 24))
    (run : evaluateHOLFiniteState state (payloadAt 14) = (some (.returned value),post)) :
    evaluateHOLFiniteState (payloadExtraDataHeaderPost state payload pointer extra transactions) (payloadAt 16) =
      (some (.returned value),post) := by
  rw [evaluate_payload_extra_data_header_source,evaluateHOLFiniteState_seq_line780,
    evaluate_payload_extra_data_header_writes state payload pointer extra transactions atPayload atPointer atExtra atTransactions
      pointerDomain lengthDomain] at run
  exact run

/-- A returned suffix passes the extra-data guard and reaches transaction-list
decoding with the exact two-word header update. -/
theorem payload_extra_data_prefix_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload pointer extra transactions : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atExtra : state.locals.lookup (ofString "o_extra") = some (.val (.word extra)))
    (atTransactions : state.locals.lookup (ofString "o_txs") = some (.val (.word transactions)))
    (pointerDomain : state.memaddrs (payload + 16)) (lengthDomain : state.memaddrs (payload + 24))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 13) = (some (.returned value),post)) :
    (transactions - extra).toNat ≤ 32 ∧
      evaluateHOLFiniteState (payloadExtraDataHeaderPost state payload pointer extra transactions) (payloadAt 16) =
        (some (.returned value),post) := by
  obtain ⟨small,tail⟩ := payload_extra_data_guard_returned state post extra transactions value atExtra atTransactions code run
  exact ⟨small,payload_extra_data_header_returned state post payload pointer extra transactions value
    atPayload atPointer atExtra atTransactions pointerDomain lengthDomain tail⟩

#print axioms evaluate_payload_extra_data_header_writes
#print axioms payload_extra_data_header_readback
#print axioms payload_extra_data_header_returned
#print axioms payload_extra_data_prefix_returned
end InitECandidate.Runtime
