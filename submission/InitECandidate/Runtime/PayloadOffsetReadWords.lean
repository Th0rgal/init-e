import Flapjack.Pancake.Semantics.PanSem.EvalFinite
import InitECandidate.Runtime.PayloadOffsetReadScopes
import InitECandidate.Runtime.PanDecReturnedScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful ordinary word operation has a scalar word result. -/
theorem evaluated_binop_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (operator : BinOp) (arguments : List (ExpHOL 64)) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.op operator arguments) = some value) :
    ∃ word : BitVec 64, value = .val (.word word) := by
  change evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
    (.op operator arguments) = some value at evaluated
  rw [evalHOLFinite_op] at evaluated
  dsimp only [evalListHOLFinite] at evaluated
  cases args : @evalListHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none => simp [args] at evaluated
  | some values =>
    rw [args] at evaluated
    dsimp only at evaluated
    split at evaluated
    · cases operation : wordOpHOL operator (values.map valueWord) with
      | none => simp [operation] at evaluated
      | some word => exact ⟨word,by simpa [operation] using evaluated.symm⟩
    · simp at evaluated

theorem payload_offset_read_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (offset : BitVec 64) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (payloadOffsetRead offset) = some value) :
    ∃ word : BitVec 64, value = .val (.word word) :=
  evaluated_binop_word state .or _ value evaluated

/-- A returned offset-reading prefix itself supplies the four successful word
initializers; no byte-read evaluation assumptions remain. -/
theorem payload_offset_reads_returned_words {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (payloadAt 4) = (some (.returned value),post)) :
    ∃ (extra txs withdrawals balance : BitVec 64) (output : PanSemStateFiniteExact 64 F),
      let entry := setVarHOLFinite (ofString "o_bal") (.val (.word balance))
        (setVarHOLFinite (ofString "o_wd") (.val (.word withdrawals))
          (setVarHOLFinite (ofString "o_txs") (.val (.word txs))
            (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state)))
      evaluateHOLFiniteState entry (payloadAt 8) = (some (.returned value),output) ∧
        post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  rw [source_payload_offset_read_0] at run
  obtain ⟨v1,out1,read1,run1,restore1⟩ := evaluate_dec_returned_scope state _
    (ofString "o_extra") .one (payloadOffsetRead 436) (payloadAt 5) value run
  obtain ⟨extra,rfl⟩ := payload_offset_read_word state 436 _ read1
  rw [source_payload_offset_read_1] at run1
  obtain ⟨v2,out2,read2,run2,restore2⟩ := evaluate_dec_returned_scope (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state) _
    (ofString "o_txs") .one (payloadOffsetRead 504) (payloadAt 6) value run1
  obtain ⟨txs,rfl⟩ := payload_offset_read_word (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state) 504 _ read2
  rw [source_payload_offset_read_2] at run2
  obtain ⟨v3,out3,read3,run3,restore3⟩ := evaluate_dec_returned_scope (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state)) _
    (ofString "o_wd") .one (payloadOffsetRead 508) (payloadAt 7) value run2
  obtain ⟨withdrawals,rfl⟩ := payload_offset_read_word (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state)) 508 _ read3
  rw [source_payload_offset_read_3] at run3
  obtain ⟨v4,out4,read4,run4,restore4⟩ := evaluate_dec_returned_scope (setVarHOLFinite (ofString "o_wd") (.val (.word withdrawals)) (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state))) _
    (ofString "o_bal") .one (payloadOffsetRead 528) (payloadAt 8) value run3
  obtain ⟨balance,rfl⟩ := payload_offset_read_word (setVarHOLFinite (ofString "o_wd") (.val (.word withdrawals)) (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state))) 528 _ read4
  refine ⟨extra,txs,withdrawals,balance,out4,run4,?_,?_,?_⟩
  all_goals rw [restore1,restore2,restore3,restore4]

#print axioms evaluated_binop_word
#print axioms payload_offset_reads_returned_words
end InitECandidate.Runtime
