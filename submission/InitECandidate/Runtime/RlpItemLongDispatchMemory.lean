import InitECandidate.Runtime.RlpItemLongStringMemory
import InitECandidate.Runtime.RlpItemLongDispatchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_long_after_load_returned_memory {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (_totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (_nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemAfterByte = (some (.returned value),final)) :
    final.memory = state.memory := by
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
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 191) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,upper]
  have terminal := evaluate_rlpItem_long_string_terminal state pointer header pointerLocal headerLocal lower upper code ticks
  rw [source_rlpItem_single_byte,evaluateHOLFiniteState_seq_line780,first] at run
  dsimp only at run
  rw [source_rlpItem_short_dispatch,evaluateHOLFiniteState_seq_line780,second] at run
  dsimp only at run
  rw [source_rlpItem_long_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at run
  cases selected : evaluateHOLFiniteState state rlpItemLongString with
  | mk result post =>
    rw [selected] at terminal run
    cases result with
    | none => exact False.elim (terminal rfl)
    | some stopped =>
      have equal := Prod.mk.inj run
      have stoppedEq := Option.some.inj equal.1
      subst stopped
      have postEq := equal.2
      subst post
      exact rlpItem_long_string_returned_memory state final pointer header value pointerLocal headerLocal code selected

#print axioms rlpItem_long_after_load_returned_memory
end InitECandidate.Runtime
