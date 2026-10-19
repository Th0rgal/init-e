import InitECandidate.Runtime.HtrPayloadWithdrawalAllocationSuffixBound
import InitECandidate.Runtime.HtrPayloadWithdrawalMetadataReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_htrPayload_withdrawal_metadata_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk array heap count chunks mark payload requests length raw out oldIndex : BitVec 64)
    (rawLocal : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (lengthBound : length.toNat ≤ 134217712) (markBound : mark.toNat ≤ 33806089496)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (markLocal : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (payloadChunks : payload.toNat + 72 < chunks.toNat)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (chunkGlobal : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (countBound : count.toNat ≤ 134217712)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    (code : state.code = originalRuntimeCode)
    (withdrawals : RlpSliceEntry state payload (3#64) array count)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word oldIndex)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (entry : RlpSliceEntry state payload (4#64) requests length)
    (budget : 2 + ((count.toNat * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadPostWithdrawalCost) ≤ state.clock) :
    RunBounded state (htrPayloadAt 24)
      (2 + ((count.toNat * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadPostWithdrawalCost)) := by
  have reached := htrPayload_withdrawal_metadata_reaches state payload array count payloadLocal withdrawals
  have combined := evaluate_reaches_terminal_bounded state (htrPayloadAt 24) (htrPayloadAt 26) _ 0 _
    (by simpa only [Nat.zero_add] using budget) reached (by
      intro next equal remaining
      subst next
      let ready := setVarHOLFinite (ofString "nwd") (.val (.word count))
        (setVarHOLFinite (ofString "wd") (.val (.word array)) state)
      change RunBounded ready (htrPayloadAt 26) _
      have keep (key : MlS) (notArray : key ≠ ofString "wd") (notCount : key ≠ ofString "nwd") :
          ready.locals.lookup key = state.locals.lookup key := by
        simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notArray,Ne.symm notCount]
      have arrayLocal : ready.locals.lookup (ofString "wd") = some (.val (.word array)) := by
        simp (config := {decide := true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have countLocal : ready.locals.lookup (ofString "nwd") = some (.val (.word count)) := by
        simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have keptEntry := entry.after_frame state ready payload (4#64) requests length rfl rfl rfl
      exact runBounded_htrPayload_withdrawal_allocation_suffix ready pointer accelerator zeroHashes chunk array heap count
        chunks mark payload requests length raw out oldIndex
        ((keep _ (by decide) (by decide)).trans rawLocal) ((keep _ (by decide) (by decide)).trans outLocal)
        ((keep _ (by decide) (by decide)).trans payloadLocal) lengthBound markBound
        ((keep _ (by decide) (by decide)).trans chunksLocal) ((keep _ (by decide) (by decide)).trans markLocal)
        chunksAligned chunksFits payloadChunks chunkAligned chunkPayload chunkGlobal countBound heapAligned heapFits payloadHeap
        accelAligned accelPayload pointerPayload code arrayLocal countLocal ((keep _ (by decide) (by decide)).trans indexLocal)
        heapGlobal pointerGlobal accelGlobal zeroGlobal keptEntry remaining)
  simpa only [RunBounded,Nat.zero_add] using combined

#print axioms runBounded_htrPayload_withdrawal_metadata_suffix
end InitECandidate.Runtime
