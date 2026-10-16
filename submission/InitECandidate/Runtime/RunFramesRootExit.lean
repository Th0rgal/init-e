import InitECandidate.Runtime.RunFramesFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def runFramesRootExit : ProgHOL 64 :=
  .seq (.assign .global (ofString "ev") (continuationLoad 0))
    (.seq (.assign .global (ofString "cur_cont") (continuationLoad 8))
      (.assign .local (ofString "go") (.const 0)))

noncomputable def runFramesRootExitPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (parent previous : BitVec 64) :=
  setVarHOLFinite (ofString "go") (.val (.word 0))
    (setKvarHOLFinite .global (ofString "cur_cont") (.val (.word previous))
      (setKvarHOLFinite .global (ofString "ev") (.val (.word parent)) state))

/-- Top-level frame completion restores both global pointers and clears go.
It neither consumes clock nor changes memory. -/
theorem evaluate_runFrames_root_exit {F : Type} (state : PanSemStateFiniteExact 64 F)
    (continuation frame parent previous go : BitVec 64)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (goLocal : state.locals.lookup (ofString "go") = some (.val (.word go)))
    (parentDomain : state.memaddrs (continuation + 0))
    (parentMemory : state.memory (continuation + 0) = .word parent)
    (previousDomain : state.memaddrs (continuation + 8))
    (previousMemory : state.memory (continuation + 8) = .word previous) :
    evaluateHOLFiniteState state runFramesRootExit =
      (none,runFramesRootExitPost state parent previous) := by
  classical
  have previousDomainLiteral : state.memaddrs (continuation + (8#64)) := previousDomain
  have previousMemoryLiteral : state.memory (continuation + (8#64)) = .word previous := previousMemory
  have parentDomainZero : state.memaddrs continuation := by simpa using parentDomain
  have parentMemoryZero : state.memory continuation = .word parent := by simpa using parentMemory
  have names : ofString "ev" ≠ ofString "cur_cont" := by decide
  have names' := Ne.symm names
  simp [runFramesRootExit,runFramesRootExitPost,evaluateHOLFiniteState_seq_line780,
    evaluateHOLFiniteState_assign,continuationLoad,evalHOLExact,evalListHOLExact,toExact,
    contGlobal,frameGlobal,goLocal,parentDomainZero,parentMemoryZero,
    previousDomainLiteral,previousMemoryLiteral,wordOpHOL,wordOp,valueIsWord,valueWord,
    isWfShapeExactHOL,memLoadHOLExact,isValidValueHOLExact,lookupKvarHOLExact,
    shapeEqHOL,shapeOfHOLExact,setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite,
    HolFiniteMapExact.lookup_update,FUPDATE,names,names']

/-- After the real epilogue returns, a top-level continuation takes the
    pointer-restoration path and clears go. -/
theorem evaluate_runFrames_root_finish {F : Type} (state afterEpilogue : PanSemStateFiniteExact 64 F)
    (continuation frame parent previous go : BitVec 64)
    (epilogue : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "frame_epilogue") []) = (none,afterEpilogue))
    (contGlobal : afterEpilogue.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : afterEpilogue.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (goLocal : afterEpilogue.locals.lookup (ofString "go") = some (.val (.word go)))
    (kindDomain : afterEpilogue.memaddrs (continuation + 16))
    (kindMemory : afterEpilogue.memory (continuation + 16) = .word 0)
    (parentDomain : afterEpilogue.memaddrs (continuation + 0))
    (parentMemory : afterEpilogue.memory (continuation + 0) = .word parent)
    (previousDomain : afterEpilogue.memaddrs (continuation + 8))
    (previousMemory : afterEpilogue.memory (continuation + 8) = .word previous) :
    evaluateHOLFiniteState state runFramesFinishBranch =
      (none,runFramesRootExitPost afterEpilogue parent previous) := by
  rw [runFrames_finish_shape]
  simp only [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip,epilogue]
  rw [evaluate_loaded_word_ite afterEpilogue (continuationLoad 16) 0 0 .equal
    (eval_continuationLoad afterEpilogue continuation 16 0 contGlobal kindDomain kindMemory)]
  simp only [Compiler.Encoders.Asm.wordCmpHOL]
  exact evaluate_runFrames_root_exit afterEpilogue continuation frame parent previous go
    contGlobal frameGlobal goLocal parentDomain parentMemory previousDomain previousMemory

#print axioms evaluate_runFrames_root_finish
#print axioms evaluate_runFrames_root_exit
end InitECandidate.Runtime
