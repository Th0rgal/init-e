import InitECandidate.Runtime.HtrPayloadWithdrawalSuffixMemory
import InitECandidate.Runtime.HtrPayloadWithdrawalAllocationSuffixBound
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful traversal of the actual withdrawal allocation and counter reset
creates the loop geometry; allocations that stop never reach this returned suffix. -/
theorem htrPayload_withdrawal_allocation_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (arrayLocal : state.locals.lookup (ofString "wd") = some (.val (.word array)))
    (countLocal : state.locals.lookup (ofString "nwd") = some (.val (.word count)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word oldIndex)))
    (entry : RlpSliceEntry state payload (4#64) requests length)
    (budget : 2 + ((count.toNat * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadPostWithdrawalCost) ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt 26) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have reached := htrPayload_withdrawal_allocation_frame_reaches state array heap count chunks oldIndex
    arrayLocal countLocal locals.2.2.1 indexLocal layout.atHeap layout.heapFits layout.code (by omega)
  obtain ⟨next,facts,spent,_,agreement,normal⟩ := reaches_returned_continuation state (htrPayloadAt 26) (htrPayloadAt 28)
    _ 2 value reached (by rw [run])
  obtain ⟨valid,chunksKept,installed,cap,memory,domain,globals,keep,covers,aligned⟩ := facts
  have entryKept := entry.after_frame state next payload (4#64) requests length domain (congrFun memory _) (congrFun memory _)
  have nextBefore : watched.toNat < (allocationEnd heap (htrPayloadTxAllocationSize count)).toNat := by
    have := layout.heapBefore
    omega
  have nextLayout := layout.after_heap_restore globals (installed.trans layout.code.symm) aligned cap nextBefore
  rw [htrPayload_tx_allocation_size count countBound] at covers
  let tailCost := (count.toNat * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadPostWithdrawalCost
  have remaining : tailCost ≤ next.clock := by
    change 2 + tailCost ≤ state.clock at budget
    generalize tailCost = cost at budget ⊢
    omega
  have suffix := htrPayload_withdrawal_suffix_returned_memory next (evaluateHOLFiniteState next (htrPayloadAt 28)).2
    sha accelerator zeroHashes chunk array heap (allocationEnd heap (htrPayloadTxAllocationSize count)) count chunks mark outerMark
    payload requests length raw out watched count.toNat value nextLayout
    ⟨(keep _ (by decide) (by decide)).trans locals.1,(keep _ (by decide) (by decide)).trans locals.2.1,
      chunksKept,(keep _ (by decide) (by decide)).trans locals.2.2.2⟩
    ((keep _ (by decide) (by decide)).trans outerLocal) ((keep _ (by decide) (by decide)).trans markLocal)
    markAligned markBound watchedMark lengthBound countBound chunksAligned chunksFits payloadChunks watchedChunks
    layout.heapAligned (by omega) payloadHeap layout.heapBefore (by omega) chunkPayload accelPayload shaPayload valid entryKept
    remaining (Prod.ext normal rfl)
  have outputMemory : post.memory = (evaluateHOLFiniteState next (htrPayloadAt 28)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [outputMemory,suffix]
  exact congrFun memory watched

#print axioms htrPayload_withdrawal_allocation_suffix_returned_memory
end InitECandidate.Runtime
