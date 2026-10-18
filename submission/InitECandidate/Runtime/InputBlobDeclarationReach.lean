import InitECandidate.Runtime.InputBlobContinuationBound
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem evaluate_inputBlob_declaration_reaches {F : Type}
    (state : PanSemStateFiniteExact 64 F) (name : MlS) (pointer : BitVec 64)
    (continuation : ProgHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (heapBound : pointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : inputBlobBodyCost + 1 ≤ state.clock) :
    Reaches state (.decCall name (.comb [.one,.one]) (ofString "input_blob") [] continuation)
      (InputBlobReady state name pointer) (inputBlobBodyCost + 1) continuation := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have bounded := evaluate_inputBlob_body_bounded entry pointer heap heapBound code
    (by change inputBlobBodyCost ≤ state.clock - 1; omega)
  have lookup := pan_no_args_shape_lookup state.code.lookup (ofString "input_blob")
    (sourceFunctionBody Guest.guestFn_input_blob) (.comb [.one,.one])
    (by rw [code]; exact originalRuntimeCode_inputBlob_lookup)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_input_blob) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    obtain ⟨spent,remaining,noTimeout⟩ := bounded
    have spent' : state.clock ≤ post.clock + (inputBlobBodyCost + 1) := by
      change state.clock - 1 ≤ post.clock + inputBlobBodyCost at spent
      omega
    have remaining' : post.clock ≤ state.clock := by
      change post.clock ≤ state.clock - 1 at remaining
      omega
    have fixed : fixClockHOLFinite entry (result,post) = (result,post) := by
      simp [fixClockHOLFinite,Nat.not_lt.mpr remaining]
    unfold Reaches
    rw [evaluateHOLFiniteState_decCall_total]
    simp only [evalListHOLFinite,evalListHOLExact]
    rw [lookup]
    dsimp only
    rw [if_neg (show state.clock ≠ 0 by omega),bodyRun,fixed]
    dsimp only
    cases result with
    | none =>
      right
      exact ⟨.error,rfl,by simp,spent',remaining',by simp⟩
    | some result =>
      cases result with
      | returned value =>
        obtain ⟨length,small,returnedValue,globals,capped,covers,aligned,domain,installed⟩ :=
          inputBlob_body_returned entry post pointer value heap heapBound code bodyRun
        rw [returnedValue]
        simp only [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL,List.map_cons,
          List.map_nil,beq_self_eq_true,Bool.true_and,if_true]
        left
        let ready := setVarHOLFinite name (.rStruct [.val (.word pointer),.val (.word length)])
          {post with locals := state.locals}
        refine ⟨ready,⟨length,small,rfl,globals,capped,covers,aligned,installed,domain⟩,
          spent',remaining',?_⟩
        exact scoped_restore (evaluateHOLFiniteState ready continuation) _
      | timeOut => exact False.elim (noTimeout rfl)
      | _ =>
        right
        exact ⟨_,rfl,by simp,spent',remaining',by simp⟩

#print axioms evaluate_inputBlob_declaration_reaches
end InitECandidate.Runtime
