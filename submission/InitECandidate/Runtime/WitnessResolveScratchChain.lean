import InitECandidate.Runtime.WitnessScratchChainHeadFrame
import InitECandidate.Runtime.WitnessResolveModeHeapFrame
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_resolve_mode_normal_scratch_chain {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer : BitVec 64)
    (ceiling inputLimit : Nat)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (heapAligned : heapPointer.toNat%8=0)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word childArray)
    (atSlot : s.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (slice : RlpSliceEntry s childArray slot pointer length)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (built : NodedbTableAt s table dbHeap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (tableAbove : ceiling ≤ table.toNat) (arrayAbove : ceiling ≤ array.toNat)
    (arrayEnd : array.toNat + total.toNat*16 ≤ dbHeap.toNat)
    (spanLo : input.toNat ≤ pointer.toNat)
    (spanHi : pointer.toNat+length.toNat ≤ input.toNat+inputLength.toNat)
    (spanSize : length.toNat ≤ inputLength.toNat)
    (budget : resolveStepBodyCost length.toNat + 1 ≤ s.clock)
    (upper : Nat) (upperBeforeHeap : upper≤heapPointer.toNat)
    (chain : WitnessScratchChain s upper ceiling top) (nonempty : top≠0)
    (run : evaluateHOLFiniteState s decodeWitnessNodeResolveMode=(none,post)) :
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    post.locals.lookup (ofString "top")=some (.val (.word top)) ∧
    WitnessScratchChain post upper scratch.toNat top ∧
    ∃ nextHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      heapPointer.toNat≤nextHeap.toNat ∧ nextHeap.toNat≤33806089496 ∧ nextHeap.toNat%8=0 := by
  obtain ⟨scratchPost,framePost,nextHeap,heapPost,growth,capped,aligned,memory⟩ := witness_resolve_mode_normal_heap_frame
    s post pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer ceiling inputLimit
    atHeap heapBound heapAligned atTop arrayReadable arrayCell atSlot slice atTable inputRange lengthBound limitBound scratchGlobal
    frameGlobal code orderedFrame framePositive scratchBelow arena built entries slices tableAbove arrayAbove arrayEnd spanLo spanHi spanSize budget run
  obtain ⟨topAbove,positive,topBefore⟩ := chain.head_bounds s top upper ceiling nonempty
  have hashNat : (top+(80 : BitVec 64)).toNat=top.toNat+80 := by
    rw [BitVec.toNat_add]
    change (top.toNat+80)%2^64=top.toNat+80
    exact Nat.mod_eq_of_lt (by omega)
  have headFrame : post.memory top=s.memory top := by
    apply memory top topAbove (by omega)
    intro same
    have equal:=congrArg BitVec.toNat same
    rw [hashNat] at equal;omega
  have olderFrame (watched : BitVec 64) (above : top.toNat+88≤watched.toNat) (below : watched.toNat<upper) :
      post.memory watched=s.memory watched := by
    apply memory watched (by omega) (by omega)
    intro same
    have equal:=congrArg BitVec.toNat same
    rw [hashNat] at equal;omega
  have topKept := evaluate_avoidsLocal_flowing (ofString "top") decodeWitnessNodeResolveMode
    (by rw [source_witness_resolve_mode,source_witness_resolve_call,source_witness_resolve_tail];decide) s
    (by rw [run];exact Or.inl rfl)
  rw [run] at topKept
  exact ⟨scratchPost,framePost,topKept.trans atTop,
    chain.after_head_frame s post top upper ceiling scratch.toNat scratchBelow headFrame olderFrame,
    nextHeap,heapPost,growth,capped,aligned⟩

#print axioms witness_resolve_mode_normal_scratch_chain
end InitECandidate.Runtime
