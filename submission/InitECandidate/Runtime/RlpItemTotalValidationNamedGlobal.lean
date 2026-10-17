import InitECandidate.Runtime.RlpItemTotalContinuation
import InitECandidate.Runtime.RlpValidationPublicCallNamedGlobal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the actual item-total validation branch retains the
entry scratch and frame globals, for both lists and non-list items. -/
theorem rlpItemTotal_validation_normal_named_global {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (watched : MlS) (different : ofString "scratch_ptr" ≠ watched)
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
    (budget : (2 * length.toNat + 1) * 15 + 5 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemTotalValidation = (none,post)) :
    post.globals.lookup watched = state.globals.lookup watched := by
  rw [source_rlpItemTotal_validation,evaluateHOLFiniteState_ite] at run
  have fields := valid.fields header payload kind length
  rcases fields.1 with nonList | list
  · subst kind
    have guard : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0)) = some (.val (.word 0)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL]
    rw [guard] at run
    simp only [evaluateHOLFiniteState_skip] at run
    have same := (Prod.mk.inj run).2
    rw [← same]
  · subst kind
    have guard : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0)) = some (.val (.word 1)) := by
      simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL]
    rw [guard] at run
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at run
    have range := rlpItemTotal_payload_range pointer length header payload 1 valid noWrap (by omega)
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.op .add [.var .local (ofString "p"),.rfield 0 (.var .local (ofString "h"))],.rfield 1 (.var .local (ofString "h"))] =
        some [.val (.word (pointer + header)),.val (.word payload)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    exact rlpValidation_call_normal_named_global state post watched different _ (pointer + header) payload scratch frame ceiling inputLimit args
      range.1 (by omega) limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega) run

#print axioms rlpItemTotal_validation_normal_named_global
end InitECandidate.Runtime
