import InitECandidate.Runtime.HtrNewPayloadSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The five actual stateless-input fields read by the initial hash. -/
structure HtrNewPayloadHeader {F : Type} (state : PanSemStateFiniteExact 64 F)
    (si payload blobs count parentRoot requests : BitVec 64) : Prop where
  payloadDomain : state.memaddrs (si + (0#64))
  blobsDomain : state.memaddrs (si + (8#64))
  countDomain : state.memaddrs (si + (16#64))
  parentDomain : state.memaddrs (si + (24#64))
  requestsDomain : state.memaddrs (si + (32#64))
  payloadCell : state.memory (si + (0#64)) = .word payload
  blobsCell : state.memory (si + (8#64)) = .word blobs
  countCell : state.memory (si + (16#64)) = .word count
  parentCell : state.memory (si + (24#64)) = .word parentRoot
  requestsCell : state.memory (si + (32#64)) = .word requests
  countBound : count.toNat ≤ 134217712

theorem HtrNewPayloadHeader.after_frame {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {si payload blobs count parentRoot requests : BitVec 64}
    (header : HtrNewPayloadHeader state si payload blobs count parentRoot requests)
    (domain : post.memaddrs = state.memaddrs)
    (memory : ∀ offset : BitVec 64, offset.toNat ≤ 32 → post.memory (si + offset) = state.memory (si + offset)) :
    HtrNewPayloadHeader post si payload blobs count parentRoot requests :=
  ⟨by rw [domain]; exact header.payloadDomain,by rw [domain]; exact header.blobsDomain,
   by rw [domain]; exact header.countDomain,by rw [domain]; exact header.parentDomain,
   by rw [domain]; exact header.requestsDomain,
   (memory _ (by decide)).trans header.payloadCell,(memory _ (by decide)).trans header.blobsCell,
   (memory _ (by decide)).trans header.countCell,(memory _ (by decide)).trans header.parentCell,
   (memory _ (by decide)).trans header.requestsCell,header.countBound⟩

theorem htrNewPayload_blobs_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (si chunks payload blobs count parentRoot record : BitVec 64)
    (header : HtrNewPayloadHeader state si payload blobs count parentRoot record)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks))) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrNewPayloadBlobsArguments =
      some [.val (.word blobs),.val (.word count),.val (.word count),.val (.word (chunks + (32#64)))] := by
  simp [htrNewPayloadBlobsArguments,htrNewPayloadRead,htrNewPayloadAddress,evalListHOLExact,evalHOLExact,atSi,atChunks,
    wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
    header.blobsDomain,header.countDomain,header.blobsCell,header.countCell]

#print axioms HtrNewPayloadHeader.after_frame
#print axioms htrNewPayload_blobs_arguments
end InitECandidate.Runtime
