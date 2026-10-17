import InitECandidate.Runtime.RlpValidationStepArena
import InitECandidate.Runtime.RlpValidationParseFlag
import InitECandidate.Runtime.RlpValidationPopScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normal original validator step either clears its loop flag or preserves
its original value through parsing or a saved-interval pop. -/
theorem rlpValidation_step_flag {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop scratch frame : BitVec 64) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (stack : RlpValidationStack state.memory scratch.toNat frames)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 14 ≤ state.clock)
    (orderedFrame : frame ≤ scratch)
    (ceiling : Nat) (scratchBelow : scratch.toNat ≤ ceiling)
    (stackCeiling : RlpValidationStackCeiling ceiling frames)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (flag : BitVec 64)
    (flagLocal : state.locals.lookup (ofString "go") = some (.val (.word flag)))
    (run : evaluateHOLFiniteState state rlpValidationStep = (none,post)) :
    post.locals.lookup (ofString "go") = some (.val (.word 0)) ∨
      post.locals.lookup (ofString "go") = state.locals.lookup (ofString "go") := by
  by_cases finished : position = stop
  · subst position
    cases frames with
    | nil =>
      have actual := evaluate_rlpValidation_finish_empty state stop flag positionLocal stopLocal topLocal flagLocal
      have same := (Prod.mk.inj (run.symm.trans actual)).2
      left
      rw [same]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    | cons saved rest =>
      have readable := stack.readable state stackCeiling (by
        intro address lower upper
        apply arena address _ upper
        have ordered := BitVec.le_def.mp orderedFrame
        omega)
      have domains := readable saved (by simp)
      obtain ⟨output,popRun,preserved,_⟩ := evaluate_rlpValidation_stack_pop_scope state stop stop scratch.toNat saved rest
        positionLocal stopLocal topLocal stack domains.1 domains.2.1 domains.2.2
      have actual := (evaluate_rlpValidation_step_stack_pop state stop scratch.toNat saved rest
        positionLocal stopLocal topLocal stack).trans popRun
      have same := (Prod.mk.inj (run.symm.trans actual)).2
      exact Or.inr (same ▸ preserved)
  · right
    have headerRun := (evaluate_rlpValidation_step_header state position stop positionLocal stopLocal finished).symm.trans run
    exact rlpValidation_parse_flag state post position stop scratch frame frames positionLocal stopLocal topLocal
      scratchGlobal frameGlobal code ticks orderedFrame (by
        intro address lower upper
        exact arena address lower (by omega)) headerRun

#print axioms rlpValidation_step_flag
end InitECandidate.Runtime
