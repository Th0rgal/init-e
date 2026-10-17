import InitECandidate.Runtime.RlpUncheckedDispatchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original unchecked helper returns the exact short-item encoded length
without reading payload bytes or consuming clock. -/
theorem evaluate_rlpUnchecked_short_after_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (header : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (short : header.toNat ≤ 183) :
    evaluateHOLFiniteState state rlpUncheckedAfterByte =
      (some (.returned (.val (.word (if header.toNat < 128 then 1 else (1 + header) - 128)))),emptyLocalsHOLFinite state) := by
  by_cases single : header.toNat < 128
  · have guard : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local (ofString "b")) (.const 128)) = some (.val (.word 1)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,single]
    rw [source_rlpUnchecked_single,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,single]
  · have guard : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local (ofString "b")) (.const 128)) = some (.val (.word 0)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,single]
    have shortGuard : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notLower (.const 183) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,short]
    rw [source_rlpUnchecked_single,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [if_true,evaluateHOLFiniteState_skip]
    rw [source_rlpUnchecked_short_string,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,shortGuard]
    simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,single]

/-- The short-string length computation is positive and at most 56 bytes. -/
theorem rlpUnchecked_short_value_bound (header : BitVec 64) (short : header.toNat ≤ 183) :
    0 < (if header.toNat < 128 then (1 : BitVec 64) else (1 + header) - 128).toNat ∧
      (if header.toNat < 128 then (1 : BitVec 64) else (1 + header) - 128).toNat ≤ 56 := by
  by_cases single : header.toNat < 128
  · simp [single]
  · simp only [if_neg single]
    have sum : ((1 : BitVec 64) + header).toNat = 1 + header.toNat := by
      rw [BitVec.toNat_add_of_lt (by change 1 + header.toNat < 2^64; omega)]
      rfl
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; rw [sum]; change 128 ≤ 1 + header.toNat; omega),sum]
    change 0 < 1 + header.toNat - 128 ∧ 1 + header.toNat - 128 ≤ 56
    omega

#print axioms evaluate_rlpUnchecked_short_after_load
#print axioms rlpUnchecked_short_value_bound
end InitECandidate.Runtime
