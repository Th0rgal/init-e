import InitECandidate.Runtime.Sha256FinishLoopMemory
import InitECandidate.Runtime.MarkedHeapReturn
import InitECandidate.Runtime.PanDecWordResultScope
import InitECandidate.Runtime.VmFn_sha256_finish
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaFinish_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer out watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (aligned : out.toNat % 8 = 0) (fits : out.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_sha256_finish) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (shaFinishAt 0) = _ at run
  rw [source_shaFinish_counter] at run
  obtain ⟨inner,bodyRun,scope⟩ := evaluate_dec_word_result_scope state post (ofString "i") (.const 0)
    (0 : BitVec 64) (shaFinishAt 1) (some (.returned value)) rfl run
  rw [source_shaFinish_loop] at bodyRun
  obtain ⟨middle,normal,returned⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) _ v) bodyRun
  have frame := shaFinish_loop_normal_memory
    (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state) middle pointer out 0 watched
    (by simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atPointer)
    (by simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atOut)
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by decide) aligned fits outside code normal
  have finalMemory := evaluate_readOnly_memory (.return (.const 0)) rfl middle
  rw [returned] at finalMemory
  rw [scope]
  exact (congrFun finalMemory watched).trans frame

theorem shaFinish_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (aligned : out.toNat % 8 = 0) (fits : out.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "sha256_finish") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "sha256_finish") =
      some ([(ofString "stp",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_sha256_finish,.one) := by
    rw [code]; exact vmLookup_sha256_finish
  have lookup := pan_two_word_lookup state.code.lookup (ofString "sha256_finish") (ofString "stp") (ofString "out")
    (sourceFunctionBody Guest.guestFn_sha256_finish) pointer out (by decide) installed
  obtain ⟨value,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "sha256_finish")
    .one arguments _ _ _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "stp",.val (.word pointer))).update (ofString "out",.val (.word out)))
  exact shaFinish_body_returned_memory entry output pointer out watched value
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) aligned fits outside code bodyRun

#print axioms shaFinish_body_returned_memory
#print axioms shaFinish_call_normal_memory
end InitECandidate.Runtime
