import InitECandidate.Runtime.RlpItemLoadedGlobals
import InitECandidate.Runtime.RlpErrorCheckFlow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_body_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  by_cases zero : length = 0
  · subst length
    have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "len")) (.const 0)) = some (.val (.word 1)) := by
      simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
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
      exact rlpItem_loaded_returned_globals state post pointer length scratch frame byte ceiling inputLimit
        pointerLocal lengthLocal zero loaded inputRange lengthBound limitBound scratchGlobal frameGlobal code
        orderedFrame framePositive scratchBelow arena budget value run
    | none =>
      have check : evaluateHOLFiniteState state
          (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
            (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
        rw [evaluateHOLFiniteState_ite]
        have notZero : length ≠ BitVec.ofNat 64 0 := zero
        simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
      rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,check] at run
      dsimp only at run
      rw [evaluateHOLFiniteState_dec_total] at run
      simp [evalHOLExact,pointerLocal,loaded] at run

#print axioms rlpItem_body_returned_globals
end InitECandidate.Runtime
