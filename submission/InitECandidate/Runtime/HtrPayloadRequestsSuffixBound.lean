import InitECandidate.Runtime.HtrPayloadFinalSuffixBound
import InitECandidate.Runtime.HtrPayloadTxStepBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrPayloadRequestsArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "pl"),.const 64]),
   .load .one (.op .add [.var .local (ofString "pl"),.const 72]),
   .op .add [.var .local (ofString "ch"),.const 544]]

theorem source_htrPayload_requests : htrPayloadAt 33 =
    .seq (.call (some (none,none)) (ofString "htr_pbytes") htrPayloadRequestsArguments)
      (htrPayloadAt 34) := by rfl

theorem htrPayload_requests_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload pointer length chunks : BitVec 64)
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (entry : RlpSliceEntry state payload (4#64) pointer length) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadRequestsArguments =
      some [.val (.word pointer),.val (.word length),.val (.word (chunks + (544#64)))] := by
  have pointerDomain : state.memaddrs (payload + (64#64)) := entry.pointerDomain
  have pointerCell : state.memory (payload + (64#64)) = .word pointer := entry.pointerCell
  have lengthDomain : state.memaddrs (payload + (72#64)) := by
    simpa only [BitVec.add_assoc,show (4#64) * (16#64) + (8#64) = (72#64) by decide] using entry.lengthDomain
  have lengthCell : state.memory (payload + (72#64)) = .word length := by
    simpa only [BitVec.add_assoc,show (4#64) * (16#64) + (8#64) = (72#64) by decide] using entry.lengthCell
  simp [htrPayloadRequestsArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,payloadLocal,chunksLocal,
    wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
    pointerDomain,pointerCell,lengthDomain,lengthCell]

def htrPayloadRequestsSuffixCost : Nat := (htrPbytesBodyCost + 1) + htrPayloadFinalSuffixCost

theorem runBounded_htrPayload_requests_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload pointer length chunks out heap : BitVec 64)
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (entry : RlpSliceEntry state payload (4#64) pointer length)
    (small : length.toNat ≤ 134217712)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrPayloadRequestsSuffixCost ≤ state.clock) :
    RunBounded state (htrPayloadAt 33) htrPayloadRequestsSuffixCost := by
  rw [source_htrPayload_requests]
  have args := htrPayload_requests_arguments state payload pointer length chunks payloadLocal chunksLocal entry
  apply runBounded_discard_heap_seq state (ofString "htr_pbytes") htrPayloadRequestsArguments _ (ofString "heap_ptr") heap
    (htrPbytesBodyCost + 1) htrPayloadFinalSuffixCost
    (runBounded_htrPbytes_call state none _ pointer length (chunks + (544#64)) heap args small heapGlobal heapBound code
      (by unfold htrPayloadRequestsSuffixCost at budget; omega)) budget
  · intro next normal
    have globals := htrPbytes_call_normal_globals state next htrPayloadRequestsArguments pointer length (chunks + (544#64)) heap
      args heapGlobal code normal
    rw [globals]
    exact heapGlobal
  · intro next keep heapKept nextCode remaining
    exact runBounded_htrPayload_final_suffix next chunks out heap ((keep _).trans chunksLocal)
      ((keep _).trans outLocal) heapKept heapBound (nextCode.trans code) remaining

#print axioms source_htrPayload_requests
#print axioms htrPayload_requests_arguments
#print axioms runBounded_htrPayload_requests_suffix
end InitECandidate.Runtime
