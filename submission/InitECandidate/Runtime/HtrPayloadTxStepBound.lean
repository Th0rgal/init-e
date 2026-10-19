import InitECandidate.Runtime.HtrPayloadSource
import InitECandidate.Runtime.TransactionSliceArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_tx_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index pointer length roots : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (entry : RlpSliceEntry state array index pointer length) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadTxArguments =
      some [.val (.word pointer),.val (.word length),.val (.word (roots + index * (32#64)))] := by
  simp [htrPayloadTxArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,rootsLocal,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,List.map_cons,List.map_nil]
  rw [if_pos entry.pointerDomain,entry.pointerCell]
  have d8 : state.memaddrs (array + (index * (16#64) + (8#64))) := by
    simpa only [BitVec.add_assoc] using entry.lengthDomain
  have c8 : state.memory (array + (index * (16#64) + (8#64))) = .word length := by
    simpa only [BitVec.add_assoc] using entry.lengthCell
  rw [if_pos d8,c8]

theorem runBounded_htrPayload_tx_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index pointer length roots heap : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (entry : RlpSliceEntry state array index pointer length) (small : length.toNat ≤ 134217712)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrPbytesBodyCost + 1 ≤ state.clock) :
    RunBounded state htrPayloadTxStep (htrPbytesBodyCost + 1) := by
  unfold htrPayloadTxStep
  have first := runBounded_htrPbytes_call state none htrPayloadTxArguments pointer length (roots + index * (32#64)) heap
    (htrPayload_tx_arguments state array index pointer length roots arrayLocal indexLocal rootsLocal entry)
    small atHeap heapBound code budget
  have combined := RunBounded.seq (tail := .assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) (b := 0) first (by simpa using budget) (by
    intro next normal nextCode remaining
    exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans code) remaining)
  simpa using combined

#print axioms htrPayload_tx_arguments
#print axioms runBounded_htrPayload_tx_step
end InitECandidate.Runtime
