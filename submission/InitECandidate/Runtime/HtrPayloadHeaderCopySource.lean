import InitECandidate.Runtime.HtrPayloadSource
import InitECandidate.Runtime.MemcpyDecodedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrPayloadCopyArguments (outputOffset inputOffset : BitVec 64) : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "ch"),.const outputOffset],
   .op .add [.var .local (ofString "raw"),.const inputOffset],.const 32]

theorem htrPayload_copy_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (chunks raw outputOffset inputOffset : BitVec 64)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (rawLocal : state.locals.lookup (ofString "raw") = some (.val (.word raw))) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (htrPayloadCopyArguments outputOffset inputOffset) =
      some [.val (.word (chunks + outputOffset)),.val (.word (raw + inputOffset)),.val (.word (32#64))] := by
  simp [htrPayloadCopyArguments,evalListHOLExact,evalHOLExact,chunksLocal,rawLocal,wordOpHOL,wordOp,valueIsWord,valueWord]

theorem source_htrPayload_copy_5 : htrPayloadAt 5 =
    .seq (.call (some (none,none)) (ofString "memcpy") (htrPayloadCopyArguments (64#64) (52#64)))
      (htrPayloadAt 6) := by rfl

theorem source_htrPayload_copy_6 : htrPayloadAt 6 =
    .seq (.call (some (none,none)) (ofString "memcpy") (htrPayloadCopyArguments (96#64) (84#64)))
      (htrPayloadAt 7) := by rfl

theorem source_htrPayload_copy_8 : htrPayloadAt 8 =
    .seq (.call (some (none,none)) (ofString "memcpy") (htrPayloadCopyArguments (160#64) (372#64)))
      (htrPayloadAt 9) := by rfl

theorem source_htrPayload_copy_14 : htrPayloadAt 14 =
    .seq (.call (some (none,none)) (ofString "memcpy") (htrPayloadCopyArguments (352#64) (440#64)))
      (htrPayloadAt 15) := by rfl

theorem source_htrPayload_copy_15 : htrPayloadAt 15 =
    .seq (.call (some (none,none)) (ofString "memcpy") (htrPayloadCopyArguments (384#64) (472#64)))
      (htrPayloadAt 16) := by rfl

#print axioms htrPayload_copy_arguments
#print axioms source_htrPayload_copy_5
#print axioms source_htrPayload_copy_6
#print axioms source_htrPayload_copy_8
#print axioms source_htrPayload_copy_14
#print axioms source_htrPayload_copy_15
end InitECandidate.Runtime
