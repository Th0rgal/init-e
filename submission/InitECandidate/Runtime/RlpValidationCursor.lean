import InitECandidate.Runtime.RlpHeaderCallResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Positive bounded header consumption advances the validator cursor without
word wrap whenever the current interval is ordered. -/
theorem rlp_header_cursor_advance (position stop header payload : BitVec 64)
    (ordered : position.toNat ≤ stop.toNat)
    (positive : 0 < (header + payload).toNat)
    (bounded : (header + payload).toNat ≤ (stop - position).toNat) :
    position.toNat < (position + header + payload).toNat ∧
      (position + header + payload).toNat ≤ stop.toNat ∧
      stop.toNat - (position + header + payload).toNat < stop.toNat - position.toNat := by
  have remaining : (stop - position).toNat = stop.toNat - position.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr ordered)
  have limit := stop.isLt
  have sum : (position + (header + payload)).toNat = position.toNat + (header + payload).toNat := by
    apply BitVec.toNat_add_of_lt
    rw [remaining] at bounded
    omega
  rw [BitVec.add_assoc,sum]
  rw [remaining] at bounded
  omega

/-- The exact header fields make the original payload initializer evaluate
without a memory read or a source-clock debit. -/
theorem eval_rlp_validator_payload {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position header payload kind : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (headerLocal : state.locals.lookup (ofString "h") =
      some (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)])) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .add [.var .local (ofString "pos"),.rfield 0 (.var .local (ofString "h"))]) =
      some (.val (.word (position + header))) := by
  simp [evalHOLExact,evalListHOLExact,positionLocal,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]

/-- The original after initializer adds the actual payload length to the
payload cursor, so its arithmetic is exactly the cursor-advance lemma. -/
theorem eval_rlp_validator_after {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position header payload kind : BitVec 64)
    (payloadLocal : state.locals.lookup (ofString "payload") = some (.val (.word (position + header))))
    (headerLocal : state.locals.lookup (ofString "h") =
      some (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)])) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .add [.var .local (ofString "payload"),.rfield 1 (.var .local (ofString "h"))]) =
      some (.val (.word (position + header + payload))) := by
  simp [evalHOLExact,evalListHOLExact,payloadLocal,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]

/-- A validated header supplies the exact progress measure for the current
validator interval, and list descent strictly decreases the payload bound. -/
theorem rlp_header_progress_cursor (value : ValueHOL 64) (position stop : BitVec 64)
    (ordered : position.toNat ≤ stop.toNat)
    (valid : RlpHeaderProgress value (stop - position)) :
    ∃ header payload kind : BitVec 64,
      value = .rStruct [.val (.word header),.val (.word payload),.val (.word kind)] ∧
      (kind = 0 ∨ kind = 1) ∧ position.toNat < (position + header + payload).toNat ∧
      (position + header + payload).toNat ≤ stop.toNat ∧
      stop.toNat - (position + header + payload).toNat < stop.toNat - position.toNat ∧
      (kind = 1 → payload.toNat < stop.toNat - position.toNat) := by
  obtain ⟨header,payload,kind,shape,flag,positive,bounded,nested⟩ := valid
  obtain ⟨advances,fits,decreases⟩ := rlp_header_cursor_advance position stop header payload ordered positive bounded
  refine ⟨header,payload,kind,shape,flag,advances,fits,decreases,?_⟩
  intro list
  simpa only [BitVec.toNat_sub_of_le (BitVec.le_def.mpr ordered)] using nested list

#print axioms rlp_header_progress_cursor
#print axioms rlp_header_cursor_advance
#print axioms eval_rlp_validator_payload
#print axioms eval_rlp_validator_after
end InitECandidate.Runtime
