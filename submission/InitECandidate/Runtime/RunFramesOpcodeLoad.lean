import InitECandidate.Runtime.RunFramesIteration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Connect the dispatch argument to the authoritative byte load at code + PC.
The byte-memory premise includes the actual domain and endianness checks. -/
theorem eval_runFrames_opcode_argument {F : Type}
    (state : PanSemStateFiniteExact 64 F) (frame pc code : BitVec 64) (opcode : UInt8)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (codeDomain : state.memaddrs (frame + 48))
    (codeMemory : state.memory (frame + 48) = .word code)
    (byte : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (code + pc) = some opcode) :
    evalListHOLFinite (runFramesLoopDispatchEntry state pc)
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [runFramesOpcodeExpression] =
        some [.val (.word (BitVec.ofNat 64 opcode.toNat))] := by
  classical
  let entered := runFramesLoopDispatchEntry state pc
  have codeLoad := eval_fundingLoad entered frame 48 code frameGlobal codeDomain codeMemory
  have pcLocal : entered.locals.lookup (ofString "pc") = some (.val (.word pc)) := by
    simp [entered,runFramesLoopDispatchEntry,runFramesDispatchEntry,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  have domainLiteral : state.memaddrs (frame + (48#64)) := codeDomain
  have memoryLiteral : state.memory (frame + (48#64)) = .word code := codeMemory
  have different : ofString "err" ≠ ofString "pc" := by decide
  simp [domainLiteral,memoryLiteral,different,evalListHOLFinite,evalListHOLExact,runFramesOpcodeExpression,evalHOLExact,
    fundingLoad,toExact,frameGlobal,codeDomain,codeMemory,pcLocal,
    valueIsWord,valueWord,wordOpHOL,wordOp,byte,entered,
    runFramesLoopDispatchEntry,runFramesDispatchEntry,setVarHOLFinite,
    HolFiniteMapExact.lookup_update,FUPDATE,isWfShapeExactHOL,memLoadHOLExact]

#print axioms eval_runFrames_opcode_argument
end InitECandidate.Runtime
