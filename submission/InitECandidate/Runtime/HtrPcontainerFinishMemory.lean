import InitECandidate.Runtime.HtrPcontainerSource
import InitECandidate.Runtime.HashMemoryLayout
import InitECandidate.Runtime.HeapReleaseMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The final original container hash and outer release preserve a word
outside the SHA workspaces and final output buffer. -/
theorem htrPcontainer_finish_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes heap temporary active out mark watched : BitVec 64) (value : ValueHOL 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (atTemporary : state.locals.lookup (ofString "tmp") = some (.val (.word temporary)))
    (atActive : state.locals.lookup (ofString "act") = some (.val (.word active)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (budget : 119 ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPcontainerAt 7) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_htrPcontainer_finish] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  have frame := shaPair_call_normal_memory state middle _ sha accelerator out temporary active watched
    (by simp [evalListHOLExact,evalHOLExact,atTemporary,atActive,atOut])
    layout.atSha layout.atAccel layout.accelAligned layout.outAligned layout.accelFits layout.shaFits layout.outFits
    layout.accelOutside layout.shaOutside layout.outOutside layout.code budget normal
  have metadata := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "sha256_pair")
      [.var .local (ofString "tmp"),.var .local (ofString "act"),.var .local (ofString "out")])
  rw [normal] at metadata
  have keep := evaluate_avoidsLocal_flowing (ofString "mark")
    (.call (some (none,none)) (ofString "sha256_pair")
      [.var .local (ofString "tmp"),.var .local (ofString "act"),.var .local (ofString "out")]) rfl state
    (by rw [normal]; exact Or.inl rfl)
  rw [normal] at keep
  obtain ⟨released,release,returned⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) middle v) tail
  have keptMark : middle.locals.lookup (ofString "mark") = some (.val (.word mark)) := keep.trans atMark
  have releaseFrame := heapRelease_call_normal_memory middle released (.var .local (ofString "mark")) mark
    (metadata.1.trans layout.code) (by simp [evalListHOLExact,evalHOLExact,keptMark]) release
  have finalFrame := evaluate_readOnly_memory (.return (.const 0)) rfl released
  rw [returned] at finalFrame
  exact (congrFun finalFrame watched).trans ((congrFun releaseFrame watched).trans frame)

#print axioms htrPcontainer_finish_returned_memory
end InitECandidate.Runtime
