import InitECandidate.Runtime.RlpItemShortListReturnContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_short_list_after_load_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 191 < header.toNat) (upper : header.toNat ≤ 247)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemAfterByte = (some (.returned value),post)) :
    value = .rStruct [.val (.word 1),.val (.word (pointer + 1)),.val (.word (header - 192)),.val (.word (1 + (header - 192)))] ∧
      (header - 192).toNat < total.toNat ∧ 0 < (1 + (header - 192)).toNat ∧
      (1 + (header - 192)).toNat ≤ total.toNat := by
  have first : evaluateHOLFiniteState state
      (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
        (.return (.rstruct [.const 0,.var .local (ofString "p"),.const 1,.const 1])) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat < 128 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside,evaluateHOLFiniteState_skip]
  have second : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 183) (.var .local (ofString "b"))) rlpItemShortString .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat ≤ 183 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,outside,evaluateHOLFiniteState_skip]
  have third : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 191) (.var .local (ofString "b"))) rlpItemLongString .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat ≤ 191 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,outside,evaluateHOLFiniteState_skip]
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 247) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,upper]
  rw [source_rlpItem_single_byte,evaluateHOLFiniteState_seq_line780,first] at run
  dsimp only at run
  rw [source_rlpItem_short_dispatch,evaluateHOLFiniteState_seq_line780,second] at run
  dsimp only at run
  rw [source_rlpItem_long_dispatch,evaluateHOLFiniteState_seq_line780,third] at run
  dsimp only at run
  rw [source_rlpItem_list_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at run
  have terminal := evaluate_rlpItem_short_list_terminal state header headerLocal
  cases selected : evaluateHOLFiniteState state rlpItemShortList with
  | mk result output =>
    rw [selected] at terminal run
    cases result with
    | none => exact False.elim (terminal rfl)
    | some stopped =>
      have same := Prod.mk.inj run
      exact rlpItem_short_list_return_contract state output pointer header total value pointerLocal headerLocal totalLocal
        (by omega) upper nonzero code ticks (by rw [selected,same.1])

#print axioms rlpItem_short_list_after_load_return_contract
end InitECandidate.Runtime
