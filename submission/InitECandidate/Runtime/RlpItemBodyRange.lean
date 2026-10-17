import InitECandidate.Runtime.RlpItemLoadedRange
import InitECandidate.Runtime.RlpErrorCheckFlow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_body_return_range {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (inputRange : pointer.toNat + total.toNat < 2^64) (inputBound : total.toNat + 9 < 2^64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    RlpItemRange value pointer total := by
  by_cases zero : total = 0
  · subst total
    have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "len")) (.const 0)) = some (.val (.word 1)) := by
      simp [evalHOLExact,totalLocal,Compiler.Encoders.Asm.wordCmpHOL]
    rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at run
    have terminal := evaluate_rlpFail_call_terminal state (.const 1) 1 code (by rfl)
    have noReturn := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 1] value
    cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) with
    | mk result output =>
      rw [called] at terminal noReturn run
      cases result with
      | none => exact False.elim (terminal rfl)
      | some stopped => exact False.elim (noReturn (Prod.mk.inj run).1)
  · cases loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer with
    | some byte =>
      exact rlpItem_loaded_return_range state post pointer total byte value
        pointerLocal totalLocal zero loaded code ticks inputRange inputBound run
    | none =>
      have check : evaluateHOLFiniteState state
          (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
            (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
        rw [evaluateHOLFiniteState_ite]
        have notZero : total ≠ BitVec.ofNat 64 0 := zero
        simp [evalHOLExact,totalLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
      rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,check] at run
      dsimp only at run
      rw [evaluateHOLFiniteState_dec_total] at run
      simp [evalHOLExact,pointerLocal,loaded] at run

#print axioms rlpItem_body_return_range
end InitECandidate.Runtime
