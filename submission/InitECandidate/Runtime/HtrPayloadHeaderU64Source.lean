import InitECandidate.Runtime.HtrPayloadSource
import InitECandidate.Runtime.HtrU64DecodedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrPayloadU64Arguments (inputOffset outputOffset : BitVec 64) : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "raw"),.const inputOffset],
   .op .add [.var .local (ofString "ch"),.const outputOffset]]

theorem htrPayload_u64_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (raw chunks inputOffset outputOffset : BitVec 64)
    (rawLocal : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks))) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (htrPayloadU64Arguments inputOffset outputOffset) =
      some [.val (.word (raw + inputOffset)),.val (.word (chunks + outputOffset))] := by
  simp [htrPayloadU64Arguments,evalListHOLExact,evalHOLExact,rawLocal,chunksLocal,wordOpHOL,wordOp,valueIsWord,valueWord]

theorem source_htrPayload_u64_9 : htrPayloadAt 9 =
    .seq (.call (some (none,none)) (ofString "htr_u64_at") (htrPayloadU64Arguments (404#64) (192#64)))
      (htrPayloadAt 10) := by rfl

theorem source_htrPayload_u64_10 : htrPayloadAt 10 =
    .seq (.call (some (none,none)) (ofString "htr_u64_at") (htrPayloadU64Arguments (412#64) (224#64)))
      (htrPayloadAt 11) := by rfl

theorem source_htrPayload_u64_11 : htrPayloadAt 11 =
    .seq (.call (some (none,none)) (ofString "htr_u64_at") (htrPayloadU64Arguments (420#64) (256#64)))
      (htrPayloadAt 12) := by rfl

theorem source_htrPayload_u64_12 : htrPayloadAt 12 =
    .seq (.call (some (none,none)) (ofString "htr_u64_at") (htrPayloadU64Arguments (428#64) (288#64)))
      (htrPayloadAt 13) := by rfl

#print axioms htrPayload_u64_arguments
#print axioms source_htrPayload_u64_9
#print axioms source_htrPayload_u64_10
#print axioms source_htrPayload_u64_11
#print axioms source_htrPayload_u64_12
end InitECandidate.Runtime
