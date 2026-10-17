import InitECandidate.Runtime.RlpValidationPublicCallBound
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpItemTotalContinuation : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_item_total with | .decCall _ _ _ _ body => body | _ => .skip

def rlpItemTotalValidation : ProgHOL 64 :=
  match rlpItemTotalContinuation with | .seq body _ => body | _ => .skip

def rlpItemTotalReturn : ProgHOL 64 :=
  match rlpItemTotalContinuation with | .seq _ body => body | _ => .skip

theorem source_rlpItemTotal_continuation : rlpItemTotalContinuation = .seq rlpItemTotalValidation rlpItemTotalReturn := by
  simp only [rlpItemTotalContinuation,rlpItemTotalValidation,rlpItemTotalReturn,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpItemTotal_validation : rlpItemTotalValidation =
    .ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
      (.call (some (none,none)) (ofString "rlp_validate_items")
        [.op .add [.var .local (ofString "p"),.rfield 0 (.var .local (ofString "h"))],.rfield 1 (.var .local (ofString "h"))]) .skip := by
  simp only [rlpItemTotalValidation,rlpItemTotalContinuation,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- A sized header inside a non-wrapping input supplies a non-wrapping payload
range for the original nested validator call. -/
theorem rlpItemTotal_payload_range (pointer length header payload kind : BitVec 64)
    (valid : RlpHeaderSizedProgress (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) length)
    (noWrap : pointer.toNat + length.toNat < 2^64) (inputBound : length.toNat + 9 < 2^64) :
    (pointer + header).toNat + payload.toNat < 2^64 ∧ payload.toNat ≤ length.toNat := by
  have fields := valid.fields header payload kind length
  have sumNoWrap := rlpValidation_header_payload_no_wrap header payload length fields.2.1 fields.2.2.1 inputBound
  have consumed := fields.2.2.2.2.1
  rw [BitVec.toNat_add_of_lt sumNoWrap] at consumed
  have first : pointer.toNat + header.toNat < 2^64 := by omega
  rw [BitVec.toNat_add_of_lt first]
  exact ⟨by omega,fields.2.2.1⟩

/-- The original item-total continuation validates only list payloads and
returns the consumed size, with an input-linear budget across all outcomes. -/
theorem evaluate_rlpItemTotal_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length header payload kind scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]))
    (valid : RlpHeaderSizedProgress (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) length)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 5 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpItemTotalContinuation
    state.clock ≤ evaluated.2.clock + ((2 * length.toNat + 1) * 15 + 5) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have branchBound : state.clock ≤ (evaluateHOLFiniteState state rlpItemTotalValidation).2.clock + ((2 * length.toNat + 1) * 15 + 5) ∧
      (evaluateHOLFiniteState state rlpItemTotalValidation).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state rlpItemTotalValidation).1 ≠ some .timeOut := by
    rw [source_rlpItemTotal_validation,evaluateHOLFiniteState_ite]
    have fields := valid.fields header payload kind length
    rcases fields.1 with nonList | list
    · subst kind
      have guard : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
          (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0)) = some (.val (.word 0)) := by
        simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL]
      rw [guard]
      simp [evaluateHOLFiniteState_skip]
    · subst kind
      have guard : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
          (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0)) = some (.val (.word 1)) := by
        simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL]
      rw [guard]
      simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
      have range := rlpItemTotal_payload_range pointer length header payload 1 valid noWrap (by omega)
      have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
          [.op .add [.var .local (ofString "p"),.rfield 0 (.var .local (ofString "h"))],.rfield 1 (.var .local (ofString "h"))] =
          some [.val (.word (pointer + header)),.val (.word payload)] := by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
      have bound := evaluate_rlpValidation_call_bounded state _ (pointer + header) payload scratch frame ceiling inputLimit args
        range.1 (by omega) limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega)
      exact ⟨by omega,bound.2.1,bound.2.2⟩
  rw [source_rlpItemTotal_continuation]
  apply evaluate_sequence_straight_bounded state rlpItemTotalValidation rlpItemTotalReturn _ branchBound
  simp only [rlpItemTotalReturn,rlpItemTotalContinuation,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms rlpItemTotal_payload_range
#print axioms evaluate_rlpItemTotal_continuation_bounded
end InitECandidate.Runtime
