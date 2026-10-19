import InitECandidate.Runtime.HtrPayloadWithdrawalLoopBound
import InitECandidate.Runtime.HtrPlistChunksCallBound
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrPayloadWithdrawalHashArguments : List (ExpHOL 64) :=
  [.var .local (ofString "roots"),.var .local (ofString "nwd"),.var .local (ofString "nwd"),
    .op .add [.var .local (ofString "ch"),.const 448]]

def htrPayloadWithdrawalHashCall : ProgHOL 64 :=
  .call (some (none,none)) (ofString "htr_plist_chunks") htrPayloadWithdrawalHashArguments

theorem source_htrPayload_withdrawal_hash : htrPayloadAt 29 =
    .seq htrPayloadWithdrawalHashCall (htrPayloadAt 30) := by rfl

/-- The withdrawal loop changes only its cursor among the caller locals. -/
theorem htrPayload_withdrawal_loop_local_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (different : key ≠ ofString "i")
    (run : evaluateHOLFiniteState state (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep) = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  have supported : avoidsLocal key (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep) = true := by
    simp [avoidsLocal,htrPayloadWithdrawalStep,Ne.symm different]
  have frame := evaluate_avoidsLocal_flowing key _ supported state (by rw [run]; exact Or.inl rfl)
  simpa only [run] using frame

theorem htrPayload_withdrawal_hash_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (roots count chunks : BitVec 64)
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (countLocal : state.locals.lookup (ofString "nwd") = some (.val (.word count)))
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks))) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadWithdrawalHashArguments =
      some [.val (.word roots),.val (.word count),.val (.word count),.val (.word (chunks + (448#64)))] := by
  simp [htrPayloadWithdrawalHashArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,rootsLocal,countLocal,chunksLocal,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL]

theorem runBounded_htrPayload_withdrawal_hash {F : Type} (state : PanSemStateFiniteExact 64 F)
    (roots count chunks heap : BitVec 64)
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (countLocal : state.locals.lookup (ofString "nwd") = some (.val (.word count)))
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : count.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrPlistChunksCost + 1 ≤ state.clock) :
    RunBounded state htrPayloadWithdrawalHashCall (htrPlistChunksCost + 1) := by
  exact runBounded_htrPlistChunks_call state none htrPayloadWithdrawalHashArguments roots count count (chunks + (448#64)) heap
    (htrPayload_withdrawal_hash_arguments state roots count chunks rootsLocal countLocal chunksLocal)
    small heapGlobal heapBound code budget

#print axioms source_htrPayload_withdrawal_hash
#print axioms htrPayload_withdrawal_loop_local_frame
#print axioms htrPayload_withdrawal_hash_arguments
#print axioms runBounded_htrPayload_withdrawal_hash
end InitECandidate.Runtime
