import InitECandidate.Runtime.HtrPayloadTxStepBound
import InitECandidate.Runtime.HashRootGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_tx_step_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk array index p n roots heap watched : BitVec 64) (count : Nat)
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (entry : RlpSliceEntry state array index p n)
    (inside : index.toNat < count) (rootsAligned : roots.toNat % 8 = 0)
    (rootsFits : roots.toNat + count * 32 ≤ 33806089496) (rootsBefore : watched.toNat < roots.toNat)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ 33806089496)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrPbytesBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state htrPayloadTxStep = (none,post)) :
    post.memory watched = state.memory watched := by
  unfold htrPayloadTxStep at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "htr_pbytes") htrPayloadTxArguments) with
  | mk result middle =>
    rw [callRun] at run
    cases result with
    | some stopped => cases run
    | none =>
      dsimp only at run
      have geometry := hashRoot_output_geometry roots index count inside rootsAligned rootsFits
      have frame := htrPbytes_call_normal_memory state middle htrPayloadTxArguments pointer accelerator zeroHashes chunk p n heap
        (roots + index * (32#64)) watched
        (htrPayload_tx_arguments state array index p n roots arrayLocal indexLocal rootsLocal entry)
        atPointer atAccel atChunk chunkAligned chunkFits chunkOutside atZero hh geometry.2.1 geometry.2.2
        (Or.inl (by rw [geometry.1]; omega)) small heapAligned heapFits heapBefore accelAligned accelFits pointerFits
        accelOutside pointerOutside code budget callRun
      have memory := evaluate_readOnly_memory
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) rfl middle
      rw [run] at memory
      exact (congrFun memory watched).trans frame

#print axioms htrPayload_tx_step_normal_memory
end InitECandidate.Runtime
