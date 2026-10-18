import InitECandidate.Runtime.PayloadOffsetStores
import InitECandidate.Runtime.PanDecWordResultScope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def payloadOffsetRead (offset : BitVec 64) : ExpHOL 64 :=
  .op .or [ .loadByte (.op .add [.var .local (ofString "p"),.const offset]),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "p"),.const offset,.const 1])) (.const 8),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "p"),.const offset,.const 2])) (.const 16),
    .shift .lsl (.loadByte (.op .add [.var .local (ofString "p"),.const offset,.const 3])) (.const 24)]

theorem source_payload_offset_read_0 : payloadAt 4 =
    .dec (ofString "o_extra") .one (payloadOffsetRead 436) (payloadAt 5) := by
  simp only [payloadOffsetRead,payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_payload_offset_read_1 : payloadAt 5 =
    .dec (ofString "o_txs") .one (payloadOffsetRead 504) (payloadAt 6) := by
  simp only [payloadOffsetRead,payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_payload_offset_read_2 : payloadAt 6 =
    .dec (ofString "o_wd") .one (payloadOffsetRead 508) (payloadAt 7) := by
  simp only [payloadOffsetRead,payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_payload_offset_read_3 : payloadAt 7 =
    .dec (ofString "o_bal") .one (payloadOffsetRead 528) (payloadAt 8) := by
  simp only [payloadOffsetRead,payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Invert the four original read scopes with their actual successful word
initializers, retaining the output memory/domain across local restoration. -/
theorem payload_offset_reads_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (extra txs withdrawals balance : BitVec 64) (value : ValueHOL 64)
    (read0 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (payloadOffsetRead 436) = some (.val (.word extra)))
    (read1 : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state).toExact
      (fun address => Classical.propDecidable ((setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state).memaddrs address))
      (payloadOffsetRead 504) = some (.val (.word txs)))
    (read2 : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state)).toExact
      (fun address => Classical.propDecidable ((setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state)).memaddrs address))
      (payloadOffsetRead 508) = some (.val (.word withdrawals)))
    (read3 : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "o_wd") (.val (.word withdrawals)) (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state))).toExact
      (fun address => Classical.propDecidable ((setVarHOLFinite (ofString "o_wd") (.val (.word withdrawals)) (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state))).memaddrs address))
      (payloadOffsetRead 528) = some (.val (.word balance)))
    (run : evaluateHOLFiniteState state (payloadAt 4) = (some (.returned value),post)) :
    ∃ output, evaluateHOLFiniteState (setVarHOLFinite (ofString "o_bal") (.val (.word balance)) (setVarHOLFinite (ofString "o_wd") (.val (.word withdrawals)) (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state)))) (payloadAt 8) = (some (.returned value),output) ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  rw [source_payload_offset_read_0] at run
  obtain ⟨out1,run1,restore1⟩ := evaluate_dec_word_result_scope state _ (ofString "o_extra")
    (payloadOffsetRead 436) extra (payloadAt 5) (some (.returned value)) read0 run
  rw [source_payload_offset_read_1] at run1
  obtain ⟨out2,run2,restore2⟩ := evaluate_dec_word_result_scope (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state) _ (ofString "o_txs")
    (payloadOffsetRead 504) txs (payloadAt 6) (some (.returned value)) read1 run1
  rw [source_payload_offset_read_2] at run2
  obtain ⟨out3,run3,restore3⟩ := evaluate_dec_word_result_scope (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state)) _ (ofString "o_wd")
    (payloadOffsetRead 508) withdrawals (payloadAt 7) (some (.returned value)) read2 run2
  rw [source_payload_offset_read_3] at run3
  obtain ⟨out4,run4,restore4⟩ := evaluate_dec_word_result_scope (setVarHOLFinite (ofString "o_wd") (.val (.word withdrawals)) (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state))) _ (ofString "o_bal")
    (payloadOffsetRead 528) balance (payloadAt 8) (some (.returned value)) read3 run3
  refine ⟨out4,run4,?_,?_,?_⟩
  all_goals rw [restore1,restore2,restore3,restore4]

#print axioms payload_offset_reads_returned
end InitECandidate.Runtime
