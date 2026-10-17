import InitECandidate.Runtime.ScratchReleaseCall
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful release body execution proves the scratch assignment happened,
without needing an assumption about the old global value. -/
theorem scratchRelease_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (mark : BitVec 64) (value : ValueHOL 64)
    (markLocal : state.locals.lookup (ofString "m") = some (.val (.word mark)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_scratch_release) = (some (.returned value),post)) :
    post.memory = state.memory := by
  rw [source_scratch_release,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_assign] at run
  simp only [evalHOLExact,markLocal] at run
  by_cases valid : isValidValueHOLFinite state .global (ofString "scratch_ptr") (.val (.word mark)) = true
  · simp only [valid,if_true,setKvarHOLFinite] at run
    have actual : evaluateHOLFiniteState (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mark)) state)
        (.return (.const 0)) =
        (some (.returned (.val (.word 0))),emptyLocalsHOLFinite
          (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mark)) state)) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
    have same := (Prod.mk.inj (run.symm.trans actual)).2
    rw [same]
    rfl
  · simp only [valid] at run
    cases run

/-- A normally completed original release call restores exactly the saved
scratch global and preserves all other globals and caller locals. -/
theorem scratchRelease_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (mark : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word mark)])
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "scratch_release") [argument]) = (none,post)) :
    post.memory = state.memory := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "m",.val (.word mark))
  let entry := callEntryStateHOLFinite state callee
  have atMark : entry.locals.lookup (ofString "m") = some (.val (.word mark)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "scratch_release") =
      some ([(ofString "m",.one)],sourceFunctionBody Guest.guestFn_scratch_release,.one) := by
    rw [code]; exact originalRuntimeCode_scratchRelease_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "scratch_release") (ofString "m")
    (sourceFunctionBody Guest.guestFn_scratch_release) mark installed
  obtain ⟨value,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "scratch_release")
    [argument] [.val (.word mark)] (sourceFunctionBody Guest.guestFn_scratch_release) callee .one args lookup run
  exact memory.trans (scratchRelease_returned_memory entry output mark value atMark bodyRun)

#print axioms scratchRelease_returned_memory
#print axioms scratchRelease_normal_memory
end InitECandidate.Runtime
