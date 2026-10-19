import InitECandidate.Runtime.HtrPayloadTxBlockBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- With zero transactions the actual loop never reads the transaction-array
pointer, even at clock zero. In particular the array may be the null pointer. -/
theorem evaluate_htrPayload_empty_tx_loop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (atCount : state.locals.lookup (ofString "ntx") = some (.val (.word 0)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word 0))) :
    evaluateHOLFiniteState state (.while htrPayloadTxCondition htrPayloadTxStep) = (none,state) := by
  have guard : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadTxCondition =
      some (.val (.word 0)) := by
    rw [evalHOLFinite_eq_toExact]
    simp [htrPayloadTxCondition,evalHOLExact,atCount,atIndex,Compiler.Encoders.Asm.wordCmpHOL,
      Compiler.Encoders.Asm.holAsmSignedLess]
  rw [evaluateHOLFiniteState_while_total,guard]
  simp

/-- The empty transaction block needs only its roots/count/chunks and heap
bindings. No geometry or readable cells are required for the unused tx array. -/
theorem runBounded_htrPayload_empty_tx_block {F : Type} (state : PanSemStateFiniteExact 64 F)
    (roots chunks heap : BitVec 64)
    (atRoots : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (atCount : state.locals.lookup (ofString "ntx") = some (.val (.word 0)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word 0)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapFits : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrPlistChunksCost + 2 ≤ state.clock) :
    RunBounded state htrPayloadTxBlock (htrPlistChunksCost + 2) := by
  have hashed := runBounded_htrPayload_tx_hash state roots 0 chunks heap atRoots atCount atChunks atHeap
    (by decide) heapFits code ((Nat.le_add_right (htrPlistChunksCost + 1) 1).trans budget)
  have combined := RunBounded.seq (tail := htrPayloadTxRelease) (b := 1) hashed (by omega) (by
    intro released normal installed remaining
    apply RunBounded.ofProg _ (installed.trans code) remaining
    exact ProgBounded.call vmBound_heap_release _ _)
  unfold RunBounded at combined ⊢
  rw [htrPayloadTxBlock,evaluateHOLFiniteState_seq_line780,evaluate_htrPayload_empty_tx_loop state atCount atIndex]
  exact combined

#print axioms evaluate_htrPayload_empty_tx_loop
#print axioms runBounded_htrPayload_empty_tx_block
end InitECandidate.Runtime
