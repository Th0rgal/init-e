import InitECandidate.Runtime.HtrPayloadTxLoopExitGuarded
import InitECandidate.Runtime.HtrPayloadTxBlockReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_tx_block_normal_cursor_guarded (pointer accelerator zeroHashes chunk array roots heap input inputLength count : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayRoots : array.toNat + count.toNat * 16 ≤ roots.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (pointerFits : count ≠ 0 → pointer.toNat + 64 ≤ array.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (rank : Nat)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count state rank)
    (budget : rank * (htrPbytesBodyCost + 2) ≤ state.clock)
    (run : evaluateHOLFiniteState state htrPayloadTxBlock = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word count)) := by
  obtain ⟨middle,normal,tail⟩ := seq_normal_parts (by exact run)
  have exited := htrPayload_tx_loop_normal_guarded pointer accelerator zeroHashes chunk array roots heap input inputLength count
    small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits state middle rank code valid budget normal
  have kept := evaluate_avoidsLocal_flowing (ofString "i")
    (.seq htrPayloadTxHashCall htrPayloadTxRelease) rfl middle (by rw [tail]; exact Or.inl rfl)
  rw [tail] at kept
  exact kept.trans exited.2.1

#print axioms htrPayload_tx_block_normal_cursor_guarded
end InitECandidate.Runtime
