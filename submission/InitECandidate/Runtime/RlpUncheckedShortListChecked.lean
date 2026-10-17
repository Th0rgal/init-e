import InitECandidate.Runtime.RlpUncheckedSource
import InitECandidate.Runtime.RlpHeaderShortListContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_rlpUnchecked_short_list_after_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (header : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 192 ≤ header.toNat) (upper : header.toNat ≤ 247) :
    evaluateHOLFiniteState state rlpUncheckedAfterByte =
      (some (.returned (.val (.word ((1 + header) - 192)))),emptyLocalsHOLFinite state) := by
  have single : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.var .local (ofString "b")) (.const 128)) = some (.val (.word 0)) := by
    have outside : ¬header.toNat < 128 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside]
  have shortString : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 183) (.var .local (ofString "b"))) = some (.val (.word 0)) := by
    have outside : ¬header.toNat ≤ 183 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside]
  have longString : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 191) (.var .local (ofString "b"))) = some (.val (.word 0)) := by
    have outside : ¬header.toNat ≤ 191 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside]
  have shortList : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 247) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    have outside : header.toNat ≤ 247 := upper
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside]
  rw [source_rlpUnchecked_single,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,single]
  simp only [if_true,evaluateHOLFiniteState_skip]
  rw [source_rlpUnchecked_short_string,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,shortString]
  simp only [if_true,evaluateHOLFiniteState_skip]
  rw [source_rlpUnchecked_long_string_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,longString]
  simp only [if_true,evaluateHOLFiniteState_skip]
  rw [source_rlpUnchecked_short_list,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,shortList]
  simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact]

/-- The checked short-list parser's actual size check bounds the exact
unchecked length in the same input state. -/
theorem rlpUnchecked_short_list_checked_bound {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (header total : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 192 ≤ header.toNat) (upper : header.toNat ≤ 247)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderShortList = (some (.returned value),post)) :
    ∃ consumed : BitVec 64,
      evaluateHOLFiniteState state rlpUncheckedAfterByte =
        (some (.returned (.val (.word consumed))),emptyLocalsHOLFinite state) ∧
      0 < consumed.toNat ∧ consumed.toNat ≤ total.toNat := by
  have checked := rlpHeader_short_list_scoped_progress state post header total value
    headerLocal totalLocal lower upper nonzero code run
  have equal : ((1 : BitVec 64) + header) - 192 = 1 + (header - 192) := by
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  refine ⟨(1 + header) - 192,evaluate_rlpUnchecked_short_list_after_load state header headerLocal lower upper,?_,?_⟩
  · rw [equal]; exact checked.2.1
  · rw [equal]; exact checked.2.2

#print axioms evaluate_rlpUnchecked_short_list_after_load
#print axioms rlpUnchecked_short_list_checked_bound
end InitECandidate.Runtime
