import InitECandidate.Runtime.FrameEpilogueCall
import InitECandidate.Runtime.RunFramesRootExit
import InitECandidate.Runtime.RunFramesTerminalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful inactive root frame completes the actual loop body in one
clock, preserves memory, restores parent pointers and clears the loop flag. -/
theorem runFrames_root_terminal_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (continuation frame parent previous go : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (goLocal : state.locals.lookup (ofString "go") = some (.val (.word go)))
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word 0)
    (errorDomain : state.memaddrs (frame + 160))
    (errorMemory : state.memory (frame + 160) = .word 0)
    (kindDomain : state.memaddrs (continuation + 16))
    (kindMemory : state.memory (continuation + 16) = .word 0)
    (parentDomain : state.memaddrs (continuation + 0))
    (parentMemory : state.memory (continuation + 0) = .word parent)
    (previousDomain : state.memaddrs (continuation + 8))
    (previousMemory : state.memory (continuation + 8) = .word previous) :
    ∃ post, evaluateHOLFiniteState state runFramesLoopBody = (none,post) ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧
      post.locals.lookup (ofString "go") = some (.val (.word 0)) ∧
      post.globals.lookup (ofString "ev") = some (.val (.word parent)) ∧
      post.globals.lookup (ofString "cur_cont") = some (.val (.word previous)) := by
  classical
  let entered := setVarHOLFinite (ofString "done") (.val (.word 0)) state
  let selected := setVarHOLFinite (ofString "done") (.val (.word 1)) entered
  let afterEpilogue := {selected with clock := selected.clock - 1}
  let final := runFramesRootExitPost afterEpilogue parent previous
  let post := {final with locals := (HolFiniteMapExact.resVarEq final.locals
    (ofString "done",state.locals.lookup (ofString "done")))}
  have doneZero : entered.locals.lookup (ofString "done") = some (.val (.word 0)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have doneOne : selected.locals.lookup (ofString "done") = some (.val (.word 1)) := by
    simp [selected,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have precheck := evaluate_runFrames_inactive_precheck entered continuation frame 0 contGlobal frameGlobal
    pendingDomain pendingMemory activeDomain activeMemory doneZero
  have epilogue := evaluate_frameEpilogue_success_call selected frame code clock frameGlobal errorDomain errorMemory
  have different : ofString "done" ≠ ofString "go" := by decide
  have selectedGo : afterEpilogue.locals.lookup (ofString "go") = some (.val (.word go)) := by
    simp [afterEpilogue,selected,entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,goLocal]
  have finish := evaluate_runFrames_root_finish selected afterEpilogue continuation frame parent previous go
    epilogue contGlobal frameGlobal selectedGo kindDomain kindMemory parentDomain parentMemory
    previousDomain previousMemory
  have body := evaluate_runFrames_terminal_loop_body state selected final precheck doneOne finish
  have goZero : final.locals.lookup (ofString "go") = some (.val (.word 0)) := by
    simp [final,runFramesRootExitPost,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  refine ⟨post,body,rfl,rfl,runFrames_terminal_go_preserved state final goZero,?_,?_⟩
  · have names : ofString "cur_cont" ≠ ofString "ev" := by decide
    simp [post,final,runFramesRootExitPost,setVarHOLFinite,setKvarHOLFinite,setGlobalHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,names]
  · simp [post,final,runFramesRootExitPost,setVarHOLFinite,setKvarHOLFinite,setGlobalHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE]

/-- The successful root terminal iteration and while exit together cost two
clocks, including the loop guard and the epilogue call. -/
theorem runFrames_root_terminal_while {F : Type} (state : PanSemStateFiniteExact 64 F)
    (continuation frame parent previous go : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : 2 ≤ state.clock) (running : go ≠ 0)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (goLocal : state.locals.lookup (ofString "go") = some (.val (.word go)))
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word 0)
    (errorDomain : state.memaddrs (frame + 160))
    (errorMemory : state.memory (frame + 160) = .word 0)
    (kindDomain : state.memaddrs (continuation + 16))
    (kindMemory : state.memory (continuation + 16) = .word 0)
    (parentDomain : state.memaddrs (continuation + 0))
    (parentMemory : state.memory (continuation + 0) = .word parent)
    (previousDomain : state.memaddrs (continuation + 8))
    (previousMemory : state.memory (continuation + 8) = .word previous) :
    ∃ post, evaluateHOLFiniteState state runFramesWhile = (none,post) ∧
      post.clock = state.clock - 2 ∧ post.memory = state.memory ∧
      post.locals.lookup (ofString "go") = some (.val (.word 0)) ∧
      post.globals.lookup (ofString "ev") = some (.val (.word parent)) ∧
      post.globals.lookup (ofString "cur_cont") = some (.val (.word previous)) := by
  obtain ⟨post,body,ticks,memory,goZero,parentGlobal,previousGlobal⟩ :=
    runFrames_root_terminal_body (decClockHOLFinite state) continuation frame parent previous go
      code (by change state.clock - 1 ≠ 0; omega) contGlobal frameGlobal goLocal
      pendingDomain pendingMemory activeDomain activeMemory errorDomain errorMemory
      kindDomain kindMemory parentDomain parentMemory previousDomain previousMemory
  have bound : post.clock ≤ (decClockHOLFinite state).clock := by omega
  have loop := evaluate_runFrames_while_step state post go goLocal running (by omega) body bound
  rw [evaluate_runFrames_while_done post goZero] at loop
  have finalClock : post.clock = state.clock - 2 := by
    change post.clock = state.clock - 1 - 1 at ticks
    omega
  exact ⟨post,loop,finalClock,memory,goZero,parentGlobal,previousGlobal⟩

#print axioms runFrames_root_terminal_while
#print axioms runFrames_root_terminal_body
end InitECandidate.Runtime
