import InitECandidate.Runtime.WitnessBranchFinishParseProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete actual final-child continuation: array load, final-value parse,
occupancy/cache checks and pop restore the saved parent and deliver the branch. -/
theorem witness_branch_finish_normal_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap prev : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (prevCell : s.memory top = .word prev) (topAbove : ceiling ≤ top.toNat)
    (before : top.toNat < heap.toNat) (heapBound : heap.toNat ≤ 33806089496)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    (run : evaluateHOLFiniteState s (witnessBranchFinishAt 0) = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word prev)) ∧
      post.locals.lookup (ofString "result") = some (.val (.word heap)) ∧
      post.locals.lookup (ofString "mode") = s.locals.lookup (ofString "mode") ∧
      post.memory top = s.memory top := by
  rw [source_witness_branch_finish_entry] at run
  obtain ⟨value,output,initialized,bodyRun,postEq⟩ := evaluate_dec_normal_scope s post (ofString "arr2") .one _ (witnessBranchFinishAt 1) run
  have evalArray : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "top"),.const 24])) = some (.val (.word array)) := by
    simp [evalHOLExact,evalListHOLExact,atTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
      memLoadHOLExact,arrayReadable,arrayCell]
  rw [evalArray] at initialized
  cases initialized
  let entered := setVarHOLFinite (ofString "arr2") (.val (.word array)) s
  have localFrame (name : MlS) (different : name ≠ ofString "arr2") :
      entered.locals.lookup name = s.locals.lookup name := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  obtain ⟨topPost,resultPost,modePost,cellPost⟩ := witness_branch_finish_parse_normal_progress entered output
    array pointer length scratch frame top heap prev ceiling inputLimit
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((localFrame _ (by decide)).trans atTop) ((localFrame _ (by decide)).trans atBr)
    prevCell topAbove before heapBound (slice.after_frame s entered array 16 pointer length rfl rfl rfl)
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget bodyRun
  have otherLocal (name : MlS) (different : name ≠ ofString "arr2") :
      post.locals.lookup name = output.locals.lookup name := by
    rw [postEq]
    exact restore_other_local _ _ name _ different
  exact ⟨(otherLocal _ (by decide)).trans topPost,(otherLocal _ (by decide)).trans resultPost,
    (otherLocal _ (by decide)).trans (modePost.trans (localFrame _ (by decide))),by rw [postEq]; exact cellPost⟩

#print axioms witness_branch_finish_normal_progress
end InitECandidate.Runtime
