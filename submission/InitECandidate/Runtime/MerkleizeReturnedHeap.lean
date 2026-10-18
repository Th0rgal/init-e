import InitECandidate.Runtime.MerkleEmptyHeap
import InitECandidate.Runtime.ReadOnlyDecCallReturnedHeap
import InitECandidate.Runtime.MerkleizeCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem max_readOnly : readOnlyMemory (sourceFunctionBody Guest.guestFn_max) = true := by
  rw [sourceFunctionBody_eq_structural]
  rfl

theorem merkleTarget_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (merkleizeAt 2) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [source_merkleTarget] at run
  exact evaluate_readOnly_decCall_returned_heap state post (ofString "target") (ofString "max") .one
    _ (merkleizeAt 3) (sourceFunctionBody Guest.guestFn_max) [(ofString "a",.one),(ofString "b",.one)] .one
    heap value vmLookup_max max_readOnly code atHeap
    (fun next output nextCode nextHeap tail => merkleAfterTarget_returned_heap next output heap value nextCode nextHeap tail) run

theorem merkleCountDepth_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (merkleizeAt 1) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [source_merkleCountDepth] at run
  exact evaluate_readOnly_decCall_returned_heap state post (ofString "dn") (ofString "ceil_log2") .one
    _ (merkleizeAt 2) (sourceFunctionBody Guest.guestFn_ceil_log2) [(ofString "n",.one)] .one
    heap value originalRuntimeCode_ceilLog2_lookup ceilLog2_readOnly code atHeap
    (fun next output nextCode nextHeap tail => merkleTarget_returned_heap next output heap value nextCode nextHeap tail) run

/-- Every returned original merkleize execution restores its initial real heap
frontier. This partial-correctness fact requires no size, reserve or clock bound. -/
theorem merkleize_body_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_merkleize) =
      (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (merkleizeAt 0) = _ at run
  rw [source_merkleLimitDepth] at run
  exact evaluate_readOnly_decCall_returned_heap state post (ofString "dl") (ofString "ceil_log2") .one
    _ (merkleizeAt 1) (sourceFunctionBody Guest.guestFn_ceil_log2) [(ofString "n",.one)] .one
    heap value originalRuntimeCode_ceilLog2_lookup ceilLog2_readOnly code atHeap
    (fun next output nextCode nextHeap tail => merkleCountDepth_returned_heap next output heap value nextCode nextHeap tail) run

theorem merkleize_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer n limit out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word limit),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "merkleize") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "merkleize") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "limit",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_merkleize,.one) := by
    rw [code]
    exact originalRuntimeCode_merkleize_lookup
  have lookup := pan_four_word_lookup state.code.lookup (ofString "merkleize") (ofString "p") (ofString "n")
    (ofString "limit") (ofString "out") (sourceFunctionBody Guest.guestFn_merkleize) pointer n limit out
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "merkleize")
    .one arguments _ (sourceFunctionBody Guest.guestFn_merkleize) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "n",.val (.word n))).update (ofString "limit",.val (.word limit))).update
      (ofString "out",.val (.word out)))
  exact merkleize_body_returned_heap entry bodyPost heap value (by exact code) (by exact atHeap) bodyRun

#print axioms max_readOnly
#print axioms merkleTarget_returned_heap
#print axioms merkleCountDepth_returned_heap
#print axioms merkleize_body_returned_heap
#print axioms merkleize_call_normal_heap
end InitECandidate.Runtime
