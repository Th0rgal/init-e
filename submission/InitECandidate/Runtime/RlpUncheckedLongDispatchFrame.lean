import InitECandidate.Runtime.RlpUncheckedListDispatchFrame
import InitECandidate.Runtime.RlpUncheckedListDispatchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_rlpUnchecked_long_dispatch_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 255)
    (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpUncheckedAfterShort
    evaluated.2.memory = state.memory ∧ evaluated.2.globals = state.globals := by
  by_cases string : header.toNat ≤ 191
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notLower (.const 191) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,string]
    have bound := evaluate_rlpUnchecked_long_string_frame state pointer header pointerLocal headerLocal code
    have small : (header - 183).toNat ≤ 8 := by
      rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 183 ≤ header.toNat; omega)]
      change header.toNat - 183 ≤ 8
      omega
    have terminal := evaluate_rlpUnchecked_long_string_terminal state pointer header pointerLocal headerLocal code (by omega)
    rw [source_rlpUnchecked_long_string_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
    cases run : evaluateHOLFiniteState state rlpUncheckedLongString with
    | mk result post =>
      rw [run] at bound terminal
      cases result with
      | none => exact False.elim (terminal rfl)
      | some stopped => exact bound
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notLower (.const 191) (.var .local (ofString "b"))) = some (.val (.word 0)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,string]
    rw [source_rlpUnchecked_long_string_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [if_true,evaluateHOLFiniteState_skip]
    exact evaluate_rlpUnchecked_list_dispatch_frame state pointer header pointerLocal headerLocal code

#print axioms evaluate_rlpUnchecked_long_dispatch_frame
end InitECandidate.Runtime
