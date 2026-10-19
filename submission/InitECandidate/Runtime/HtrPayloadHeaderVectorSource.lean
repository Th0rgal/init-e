import InitECandidate.Runtime.HtrPayloadSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrPayloadVectorArguments (inputOffset length outputOffset : BitVec 64) : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "raw"),.const inputOffset],.const length,
   .op .add [.var .local (ofString "ch"),.const outputOffset]]

theorem htrPayload_vector_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (raw chunks inputOffset length outputOffset : BitVec 64)
    (rawLocal : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks))) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (htrPayloadVectorArguments inputOffset length outputOffset) =
      some [.val (.word (raw + inputOffset)),.val (.word length),.val (.word (chunks + outputOffset))] := by
  simp [htrPayloadVectorArguments,evalListHOLExact,evalHOLExact,rawLocal,chunksLocal,wordOpHOL,wordOp,valueIsWord,valueWord]

theorem source_htrPayload_vector_4 : htrPayloadAt 4 =
    .seq (.call (some (none,none)) (ofString "htr_bytes_vector") (htrPayloadVectorArguments (32#64) (20#64) (32#64)))
      (htrPayloadAt 5) := by rfl

theorem source_htrPayload_vector_7 : htrPayloadAt 7 =
    .seq (.call (some (none,none)) (ofString "htr_bytes_vector") (htrPayloadVectorArguments (116#64) (256#64) (128#64)))
      (htrPayloadAt 8) := by rfl

#print axioms htrPayload_vector_arguments
#print axioms source_htrPayload_vector_4
#print axioms source_htrPayload_vector_7
end InitECandidate.Runtime
