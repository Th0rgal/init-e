import InitECandidate.Runtime.MemcpyCallBound
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.PanDiscardNormalBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original copy body assigns no global, at any source clock. -/
theorem evaluate_memcpy_body_globals {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memcpy)).2.globals = state.globals := by
  apply HolFiniteMapExact.ext
  funext watched
  exact evaluate_avoidsGlobalAssignment watched (sourceFunctionBody Guest.guestFn_memcpy) (by simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl) state

/-- A normally completed actual copy call preserves every caller global. -/
theorem memcpy_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (destination source size : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word destination),.val (.word source),.val (.word size)])
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) = (none,post)) :
    post.globals = state.globals := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word destination))).update
      (ofString "src",.val (.word source))).update (ofString "n",.val (.word size))
  have installed : state.code.lookup (ofString "memcpy") =
      some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memcpy,.one) := by
    rw [code]; exact originalRuntimeCode_memcpy_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "memcpy") (ofString "dst") (ofString "src") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memcpy) destination source size (by decide) (by decide) (by decide) installed
  obtain ⟨value,output,bodyRun,globals,_⟩ := evaluate_discard_normal_body state post (ofString "memcpy")
    arguments [.val (.word destination),.val (.word source),.val (.word size)] (sourceFunctionBody Guest.guestFn_memcpy)
    callee .one args lookup run
  have frame := evaluate_memcpy_body_globals (callEntryStateHOLFinite state callee)
  rw [bodyRun] at frame
  exact globals.trans frame

#print axioms evaluate_memcpy_body_globals
#print axioms memcpy_call_normal_globals
end InitECandidate.Runtime
