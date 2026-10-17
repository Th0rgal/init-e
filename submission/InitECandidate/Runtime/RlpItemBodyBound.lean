import InitECandidate.Runtime.RlpItemLoadedBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Uniform bound for the complete original RLP item body, including empty
input, inaccessible first bytes, all header classes and nested rejection. -/
theorem evaluate_rlpItem_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item)
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  by_cases zero : length = 0
  · subst length
    have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "len")) (.const 0)) = some (.val (.word 1)) := by
      simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
    have failed := evaluate_rlpFail_call_bounded state (.const 1) 1 code (by simpa using (show state.clock ≠ 0 by omega)) (by rfl)
    rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
    cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) with
    | mk result post =>
      rw [run] at failed
      cases result with
      | none => exact False.elim (failed.2.2 rfl)
      | some stopped =>
        dsimp only at failed ⊢
        exact ⟨by omega,by omega,failed.2.1⟩
  · cases loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer with
    | some byte =>
      exact evaluate_rlpItem_loaded_bounded state pointer length scratch frame byte ceiling inputLimit
        pointerLocal lengthLocal zero loaded inputRange lengthBound limitBound scratchGlobal frameGlobal code
        orderedFrame framePositive scratchBelow arena budget
    | none =>
      have check : evaluateHOLFiniteState state
          (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
            (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
        rw [evaluateHOLFiniteState_ite]
        have notZero : length ≠ BitVec.ofNat 64 0 := zero
        simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
      rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,check]
      dsimp only
      rw [evaluateHOLFiniteState_dec_total]
      simp [evalHOLExact,pointerLocal,loaded]

#print axioms evaluate_rlpItem_body_bounded
end InitECandidate.Runtime
