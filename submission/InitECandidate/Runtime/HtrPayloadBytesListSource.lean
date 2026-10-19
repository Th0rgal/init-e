import InitECandidate.Runtime.HtrPayloadSource
import InitECandidate.Runtime.HtrPayloadTxStepBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrPayloadBytesListArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "pl"),.const 16]),
   .load .one (.op .add [.var .local (ofString "pl"),.const 24]),
   .const 1,.op .add [.var .local (ofString "ch"),.const 320]]

theorem source_htrPayload_bytes_list : htrPayloadAt 13 =
    .seq (.call (some (none,none)) (ofString "htr_bytes_list") htrPayloadBytesListArguments)
      (htrPayloadAt 14) := by rfl

theorem htrPayload_bytes_list_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload pointer length chunks : BitVec 64)
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (entry : RlpSliceEntry state payload (1#64) pointer length) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadBytesListArguments =
      some [.val (.word pointer),.val (.word length),.val (.word (1#64)),.val (.word (chunks + (320#64)))] := by
  have pointerDomain : state.memaddrs (payload + (16#64)) := entry.pointerDomain
  have pointerCell : state.memory (payload + (16#64)) = .word pointer := entry.pointerCell
  have lengthDomain : state.memaddrs (payload + (24#64)) := by
    simpa only [BitVec.add_assoc,show (1#64) * (16#64) + (8#64) = (24#64) by decide] using entry.lengthDomain
  have lengthCell : state.memory (payload + (24#64)) = .word length := by
    simpa only [BitVec.add_assoc,show (1#64) * (16#64) + (8#64) = (24#64) by decide] using entry.lengthCell
  simp [htrPayloadBytesListArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,payloadLocal,chunksLocal,
    wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
    pointerDomain,pointerCell,lengthDomain,lengthCell]

#print axioms source_htrPayload_bytes_list
#print axioms htrPayload_bytes_list_arguments
end InitECandidate.Runtime
