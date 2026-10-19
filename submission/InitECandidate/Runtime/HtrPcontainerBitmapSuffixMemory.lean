import InitECandidate.Runtime.HtrPcontainerMaskLoopMemory
import InitECandidate.Runtime.HtrPcontainerFinishMemory
import InitECandidate.Runtime.HtrPcontainerReturnedHeap
import InitECandidate.Runtime.GlobalsFrameComposition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual counter declaration, bitmap loop, final SHA and release keep
words outside the bitmap, SHA workspaces and final output. -/
theorem htrPcontainer_bitmap_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes heap temporary active out mark count watched : BitVec 64) (value : ValueHOL 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (atTemporary : state.locals.lookup (ofString "tmp") = some (.val (.word temporary)))
    (atActive : state.locals.lookup (ofString "act") = some (.val (.word active)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (small : count.toNat ≤ 256) (aligned : active.toNat % 8 = 0)
    (fits : active.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < active.toNat ∨ active.toNat + 32 ≤ watched.toNat)
    (budget : count.toNat + 119 ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPcontainerAt 5) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_htrPcontainer_mask] at run
  obtain ⟨bound,output,initialized,bodyRun,postEq⟩ := evaluate_dec_returned_scope state post (ofString "i") .one _ _ value run
  have boundEq : bound = .val (.word (0#64)) := by simpa [evalHOLExact] using initialized.symm
  subst boundEq
  let ready := setVarHOLFinite (ofString "i") (.val (.word (0#64))) state
  have atIndex : ready.locals.lookup (ofString "i") = some (.val (.word (0#64))) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have keep (key : MlS) (different : key ≠ ofString "i") : ready.locals.lookup key = state.locals.lookup key := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have countLocal := (keep _ (by decide)).trans atCount
  have activeLocal := (keep _ (by decide)).trans atActive
  change evaluateHOLFiniteState ready (.seq (.while htrPcontainerMaskCondition htrPcontainerMaskBody)
    (htrPcontainerAt 7)) = _ at bodyRun
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => htrPcontainer_mask_no_return ready v) bodyRun
  have memory := htrPcontainer_mask_loop_normal_memory ready middle active count 0 watched activeLocal countLocal atIndex
    (by simp) small aligned fits outside normal
  have loopBound := localBoundWhile_run (ofString "i") (ofString "n") (1#64) count
    (LocalBoundTest.below .less (Or.inl rfl)) (by change count.toNat + 1 < 2^63; omega) (by decide)
    htrPcontainer_mask_counted (by decide) (by decide) ready layout.code 0 atIndex countLocal (by decide)
    (by change (count.toNat - 0 + 1 - 1) / 1 * (0 + 0 + 1) ≤ state.clock; omega)
  rw [normal] at loopBound
  have spent : state.clock ≤ middle.clock + count.toNat := by simpa [ready,setVarHOLFinite] using loopBound.1
  have globalsFrame : OriginalGlobalsFrame (.while htrPcontainerMaskCondition htrPcontainerMaskBody) := by
    apply originalGlobalsFrame_while
    rw [source_htrPcontainer_mask_body]
    exact originalGlobalsFrame_sequence _ _ (originalGlobalsFrame_leaf _ (by intro key; rfl))
      (originalGlobalsFrame_leaf _ (by intro key; rfl))
  have normalNamed : evaluateHOLFiniteState ready (.while htrPcontainerMaskCondition htrPcontainerMaskBody) = (none,middle) := normal
  have globals := globalsFrame ready layout.code
  have metadata := evaluateHOLFiniteState_metadata ready (.while htrPcontainerMaskCondition htrPcontainerMaskBody)
  rw [normalNamed] at globals metadata
  have middleLayout := layout.transfer (by exact globals) (by exact metadata.1)
  have kept (key : MlS) (different : key ≠ ofString "i") : middle.locals.lookup key = state.locals.lookup key := by
    have frame := evaluate_avoidsLocal_flowing key (.while htrPcontainerMaskCondition htrPcontainerMaskBody)
      (by
        change avoidsLocal key htrPcontainerMaskBody = true
        rw [source_htrPcontainer_mask_body]
        have first : avoidsLocal key htrPcontainerMaskStore = true := by rfl
        rw [avoidsLocal,first]
        simp [avoidsLocal,beq_iff_eq,Ne.symm different]) ready (by rw [normalNamed]; exact Or.inl rfl)
    rw [normalNamed] at frame
    exact frame.trans (keep key different)
  have final := htrPcontainer_finish_returned_memory middle output sha accelerator zeroHashes heap temporary active out mark watched value
    middleLayout ((kept _ (by decide)).trans atTemporary) ((kept _ (by decide)).trans atActive)
    ((kept _ (by decide)).trans atOut) ((kept _ (by decide)).trans atMark) (by omega) tail
  rw [postEq]
  exact final.trans memory

#print axioms htrPcontainer_bitmap_suffix_returned_memory
end InitECandidate.Runtime
