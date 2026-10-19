import InitECandidate.Runtime.HtrPcontainerZeroSuffixMemory
import InitECandidate.Runtime.ProgressiveMemory
import InitECandidate.Runtime.ProgressiveHeapGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPcontainer_progressive_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes heap chunks temporary out mark count watched : BitVec 64) (value : ValueHOL 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atTemporary : state.locals.lookup (ofString "tmp") = some (.val (.word temporary)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (small : count.toNat ≤ 256) (aligned : temporary.toNat % 8 = 0)
    (fits : temporary.toNat + 64 ≤ 33806089496) (before : watched.toNat < temporary.toNat)
    (budget : (progressiveBodyCost + 1) + (count.toNat + 135) ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPcontainerAt 2) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_htrPcontainer_progressive] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  let args : List (ExpHOL 64) := [.var .local (ofString "ch"),.var .local (ofString "n"),.var .local (ofString "tmp")]
  have arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) args =
      some [.val (.word chunks),.val (.word count),.val (.word temporary)] := by
    simp [args,evalListHOLExact,evalHOLExact,atChunks,atCount,atTemporary]
  have frame := progressive_call_normal_memory state middle args sha accelerator zeroHashes chunks count heap temporary watched
    arguments layout.atSha layout.atAccel layout.atZero layout.atHeap aligned (by omega) (Or.inl before) (by omega)
    layout.heapAligned layout.heapFits layout.heapBefore layout.accelAligned layout.accelFits layout.shaFits
    layout.accelOutside layout.shaOutside layout.code (by omega) normal
  have globals := progressive_call_normal_globals state middle args chunks count temporary heap arguments layout.atHeap layout.code normal
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "merkleize_progressive") args)
  have bounded := runBounded_progressive_call state none args chunks count temporary heap arguments (by omega)
    layout.atHeap layout.heapFits layout.code (by omega)
  unfold RunBounded at bounded
  rw [normal] at metadata bounded
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "merkleize_progressive") args)
      rfl state (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept
  have spent : state.clock ≤ middle.clock + (progressiveBodyCost + 1) := bounded.1
  have suffix := htrPcontainer_active_suffix_returned_memory middle post sha accelerator zeroHashes heap temporary out mark count watched value
    (layout.transfer globals metadata.1) ((keep _).trans atTemporary) ((keep _).trans atOut) ((keep _).trans atMark)
    ((keep _).trans atCount) small aligned fits before (by omega) tail
  exact suffix.trans frame

#print axioms htrPcontainer_progressive_returned_memory
end InitECandidate.Runtime
