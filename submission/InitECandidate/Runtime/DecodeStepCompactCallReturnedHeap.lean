import InitECandidate.Runtime.DecodeStepCompactHeapReach
import InitECandidate.Runtime.DecodeStepPathReturnedHeap
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem remainingBudget {a b initial remaining : Nat}
    (total : a+b ≤ initial) (spent : initial ≤ remaining+a) : b ≤ remaining := by omega

theorem decode_step_compact_call_returned_heap_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (kind compactPointer compactLength consumed array secondPointer secondLength heap scratch frame pointer length : BitVec 64)
    (atItem : s.locals.lookup (ofString "pi") = some
      (.rStruct [.val (.word kind),.val (.word compactPointer),.val (.word compactLength),.val (.word consumed)]))
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (second : RlpSliceEntry s array 1 secondPointer secondLength)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (aligned : heap.toNat%8=0)
    (tableBefore : array.toNat+32 ≤ heap.toNat) (inputBound : compactLength.toNat ≤ 134217712)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ceiling inputLimit : Nat)
    (secondNoWrap : secondPointer.toNat+secondLength.toNat < 2^64)
    (secondBound : secondLength.toNat ≤ inputLimit) (limitBound : inputLimit+9 < 2^64)
    (ordered : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : (compactLength.toNat/4+7)+
      (secondLength.toNat*((2*secondLength.toNat+1)*15+19)+92637) ≤ s.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepCompactCall = (some (.returned value),post)) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      heap.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat%8=0 ∧
      ∀ watched : BitVec 64, ceiling ≤ watched.toNat → watched.toNat < heap.toNat →
        post.memory watched = s.memory watched := by
  have reached := decode_step_compact_heap_reaches s kind compactPointer compactLength consumed heap scratch frame
    atItem atHeap heapBound aligned inputBound scratchGlobal frameGlobal code (by omega)
  obtain ⟨ready,facts,spent,_,agreement,returned⟩ := reaches_returned_continuation s decodeStepCompactCall
    decodeStepCompactContinuation _ _ _ reached (by rw [run])
  obtain ⟨nibs,count,leaf,locals,heapNext,growth,capped,finishAligned,scratchNext,frameNext,codeNext,domain,memory⟩ := facts
  have other : ∀ name, name ≠ ofString "cn" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atPath : ready.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have pointerNat : (array+16#64).toNat = array.toNat+16 := by
    rw [BitVec.toNat_add_of_lt (by change array.toNat+16 < 2^64; omega)]; rfl
  have lengthNat : (array+24#64).toNat = array.toNat+24 := by
    rw [BitVec.toNat_add_of_lt (by change array.toNat+24 < 2^64; omega)]; rfl
  have pointerMemory : ready.memory (array+1*16#64) = s.memory (array+1*16#64) := by
    apply memory
    rw [show (1 : BitVec 64)*16#64 = 16#64 from by decide,pointerNat]; omega
  have lengthMemory : ready.memory (array+1*16#64+8#64) = s.memory (array+1*16#64+8#64) := by
    apply memory
    rw [show (1 : BitVec 64)*16#64 = 16#64 from by decide,BitVec.add_assoc,
      show (16#64+8#64)=24#64 from by decide,lengthNat]; omega
  have secondNext := RlpSliceEntry.after_frame s ready array 1 secondPointer secondLength second domain pointerMemory lengthMemory
  cases tailRun : evaluateHOLFiniteState ready decodeStepCompactContinuation with
  | mk result output =>
    rw [tailRun] at returned
    dsimp only at returned
    subst result
    obtain ⟨nextHeap,heapPost,growth2,capped2,aligned2,memory2⟩ := decode_step_path_returned_heap_contract
      ready output array secondPointer secondLength scratch frame pointer length (allocationEnd heap (2*compactLength))
      nibs count leaf ceiling inputLimit ((other _ (by decide)).trans atArray) secondNext secondNoWrap secondBound limitBound
      ((other _ (by decide)).trans atPointer) ((other _ (by decide)).trans atLength) atPath heapNext capped finishAligned
      scratchNext frameNext codeNext ordered framePositive scratchBelow
      (by intro address lower upper; exact (congrFun domain address).mpr (arena address lower upper))
      (remainingBudget budget spent) value tailRun
    have finalGlobals := agreement.2.2.2.1
    have finalMemory := agreement.2.2.1
    rw [run,tailRun] at finalGlobals finalMemory
    change post.globals = output.globals at finalGlobals
    change post.memory = output.memory at finalMemory
    refine ⟨nextHeap,?_,by omega,capped2,aligned2,?_⟩
    · rw [finalGlobals]; exact heapPost
    · intro watched above before
      rw [finalMemory]
      exact (memory2 watched above (by omega)).trans (memory watched before)

#print axioms decode_step_compact_call_returned_heap_contract
end InitECandidate.Runtime
