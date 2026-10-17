import InitECandidate.Runtime.RlpUncheckedLongTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual dispatch after loading a long-string header selects its branch. -/
theorem evaluate_rlpUnchecked_long_string_after_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock) :
    evaluateHOLFiniteState state rlpUncheckedAfterByte = evaluateHOLFiniteState state rlpUncheckedLongString := by
  have single : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.var .local (ofString "b")) (.const 128)) = some (.val (.word 0)) := by
    have outside : ¬header.toNat < 128 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside]
  have shortString : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 183) (.var .local (ofString "b"))) = some (.val (.word 0)) := by
    have outside : ¬header.toNat ≤ 183 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside]
  have longString : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 191) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    have outside : header.toNat ≤ 191 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside]
  rw [source_rlpUnchecked_single,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,single]
  simp only [if_true,evaluateHOLFiniteState_skip]
  rw [source_rlpUnchecked_short_string,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,shortString]
  simp only [if_true,evaluateHOLFiniteState_skip]
  rw [source_rlpUnchecked_long_string_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,longString]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
  have small : (header - 183).toNat ≤ 8 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 183 ≤ header.toNat; omega)]
    change header.toNat - 183 ≤ 8
    omega
  have terminal := evaluate_rlpUnchecked_long_string_terminal state pointer header pointerLocal headerLocal code (by omega)
  cases run : evaluateHOLFiniteState state rlpUncheckedLongString with
  | mk result post =>
    rw [run] at terminal
    cases result with
    | none => exact False.elim (terminal rfl)
    | some stopped => rfl

#print axioms evaluate_rlpUnchecked_long_string_after_load

/-- Actual dispatch after loading a long-list header selects its branch. -/
theorem evaluate_rlpUnchecked_long_list_after_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 247 < header.toNat) (upper : header.toNat ≤ 255)
    (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock) :
    evaluateHOLFiniteState state rlpUncheckedAfterByte = evaluateHOLFiniteState state rlpUncheckedLongList := by
  have single : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.var .local (ofString "b")) (.const 128)) = some (.val (.word 0)) := by
    have outside : ¬header.toNat < 128 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside]
  have shortString : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 183) (.var .local (ofString "b"))) = some (.val (.word 0)) := by
    have outside : ¬header.toNat ≤ 183 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside]
  have longString : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 191) (.var .local (ofString "b"))) = some (.val (.word 0)) := by
    have outside : ¬header.toNat ≤ 191 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside]
  have shortList : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 247) (.var .local (ofString "b"))) = some (.val (.word 0)) := by
    have outside : ¬header.toNat ≤ 247 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside]
  rw [source_rlpUnchecked_single,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,single]
  simp only [if_true,evaluateHOLFiniteState_skip]
  rw [source_rlpUnchecked_short_string,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,shortString]
  simp only [if_true,evaluateHOLFiniteState_skip]
  rw [source_rlpUnchecked_long_string_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,longString]
  simp only [if_true,evaluateHOLFiniteState_skip]
  rw [source_rlpUnchecked_short_list,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,shortList]
  simp only [if_true,evaluateHOLFiniteState_skip]

#print axioms evaluate_rlpUnchecked_long_list_after_load

end InitECandidate.Runtime
