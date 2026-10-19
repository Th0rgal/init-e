import InitECandidate.Runtime.KeccakFullBodyWindow
import InitECandidate.Runtime.KeccakFullCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual installed hash call preserves watched memory outside its three
write windows, and preserves globals in all outcomes. -/
theorem keccak_full_call_window {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output watched : BitVec 64) (arguments : List (ExpHOL 64))
    (atState : state.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word source),.val (.word size),.val (.word output)])
    (small : size.toNat ≤ 134217712)
    (code : state.code = originalRuntimeCode) (budget : size.toNat * 20 + 43 ≤ state.clock)
    (outsideState : ¬ MWin pointer 200 watched) (outsidePad : ¬ MWin pad 136 watched)
    (outsideOutput : ¬ MWin output 32 watched) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak256") arguments)).2.memory watched = state.memory watched ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak256") arguments)).2.globals = state.globals := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "p",.val (.word source))).update (ofString "n",.val (.word size))).update
      (ofString "out",.val (.word output))
  have installed : state.code.lookup (ofString "keccak256") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_keccak256,.one) := by
    rw [code]; exact originalRuntimeCode_keccak_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "keccak256") (ofString "p") (ofString "n") (ofString "out")
    (sourceFunctionBody Guest.guestFn_keccak256) source size output (by decide) (by decide) (by decide) installed
  let entry := callEntryStateHOLFinite state callee
  have frame := keccak_full_body_window entry pointer pad source size output watched atState atPad
    (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) small code
    (by change size.toNat * 20 + 42 ≤ state.clock - 1; omega)
    outsideState outsidePad outsideOutput
  exact watch_discardCall state watched (ofString "keccak256") arguments _ args _ callee .one lookup
    ⟨frame,keccak_body_globals_frame entry code⟩

#print axioms keccak_full_call_window
end InitECandidate.Runtime
