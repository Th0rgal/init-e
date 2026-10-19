import InitECandidate.Runtime.HtrPayloadWithdrawalAllocationMemory
import InitECandidate.Runtime.HtrPayloadWithdrawalMetadataReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual withdrawal metadata loads compose with allocation, loop,
release and final hashing, preserving the caller's watched memory. -/
theorem htrPayload_withdrawal_metadata_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk array heap count chunks mark outerMark payload requests length raw out oldIndex watched : BitVec 64)
    (value : ValueHOL 64)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (locals : PayloadFinalLocals state payload raw chunks out)
    (outerLocal : state.locals.lookup (ofString "mark") = some (.val (.word outerMark)))
    (markLocal : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (markAligned : mark.toNat % 8 = 0) (markBound : mark.toNat ≤ 33806089496) (watchedMark : watched.toNat < mark.toNat)
    (lengthBound : length.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (payloadChunks : payload.toNat + 72 < chunks.toNat) (watchedChunks : watched.toNat < chunks.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (shaPayload : sha.toNat + 64 ≤ payload.toNat)
    (withdrawals : RlpSliceEntry state payload (3#64) array count)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word oldIndex)))
    (entry : RlpSliceEntry state payload (4#64) requests length)
    (budget : 2 + ((count.toNat * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadPostWithdrawalCost) ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt 24) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have reached := htrPayload_withdrawal_metadata_reaches state payload array count locals.1 withdrawals
  obtain ⟨next,equal,spent,_,agreement,normal⟩ := reaches_returned_continuation state (htrPayloadAt 24) (htrPayloadAt 26)
    _ 0 value reached (by rw [run])
  subst next
  let ready := setVarHOLFinite (ofString "nwd") (.val (.word count))
    (setVarHOLFinite (ofString "wd") (.val (.word array)) state)
  have keep (key : MlS) (notArray : key ≠ ofString "wd") (notCount : key ≠ ofString "nwd") :
      ready.locals.lookup key = state.locals.lookup key := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notArray,Ne.symm notCount]
  have arrayLocal : ready.locals.lookup (ofString "wd") = some (.val (.word array)) := by
    simp (config := {decide := true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have countLocal : ready.locals.lookup (ofString "nwd") = some (.val (.word count)) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryKept := entry.after_frame state ready payload (4#64) requests length rfl rfl rfl
  have suffix := htrPayload_withdrawal_allocation_suffix_returned_memory ready (evaluateHOLFiniteState ready (htrPayloadAt 26)).2
    sha accelerator zeroHashes chunk array heap count chunks mark outerMark payload requests length raw out oldIndex watched value
    (layout.transfer rfl rfl)
    ⟨(keep _ (by decide) (by decide)).trans locals.1,(keep _ (by decide) (by decide)).trans locals.2.1,
      (keep _ (by decide) (by decide)).trans locals.2.2.1,(keep _ (by decide) (by decide)).trans locals.2.2.2⟩
    ((keep _ (by decide) (by decide)).trans outerLocal) ((keep _ (by decide) (by decide)).trans markLocal)
    markAligned markBound watchedMark lengthBound countBound chunksAligned chunksFits payloadChunks watchedChunks payloadHeap
    chunkPayload accelPayload shaPayload arrayLocal countLocal ((keep _ (by decide) (by decide)).trans indexLocal) entryKept budget
    (Prod.ext normal rfl)
  have outputMemory : post.memory = (evaluateHOLFiniteState ready (htrPayloadAt 26)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [outputMemory,suffix]
  rfl

#print axioms htrPayload_withdrawal_metadata_suffix_returned_memory
end InitECandidate.Runtime
