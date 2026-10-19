import InitECandidate.Runtime.NodedbBodyConstructorReturnedFrame
import InitECandidate.Runtime.NodedbConstructorLoopEntryWorkspace
import InitECandidate.Runtime.NodedbSuffixReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
/-- A complete actual returned builder run supplies its table pointer, live
frontier, workspace globals and old protected-memory frame. -/
theorem nodedb_whole_body_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (pointer total array statePad pad output : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word total)))
    (atArray : s.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (small : total.toNat ≤ 134217712)
    (outputAligned : output.toNat % 8 = 0)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ pointer.toNat)
    (stateEnd : statePad.toNat + 200 ≤ array.toNat) (padEnd : pad.toNat + 136 ≤ array.toNat)
    (outputEnd : output.toNat + 32 ≤ array.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (slices : ∀ j : BitVec 64, j.toNat < total.toNat → ∃ source size : BitVec 64,
      s.memaddrs (array + j * (16#64)) ∧ s.memaddrs (array + j * (16#64) + (8#64)) ∧
      s.memory (array + j * (16#64)) = .word source ∧ s.memory (array + j * (16#64) + (8#64)) = .word size ∧
      size.toNat ≤ 134217712)
    (budget : nodedbBodyCost total ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_nodedb_build) = (some (.returned value),post)) :
    value = .val (.word pointer) ∧
    post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
    post.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) ∧
    post.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) ∧
    post.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
    (∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      pointer.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
      (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 → post.memaddrs a)) ∧
    (∀ w : BitVec 64, w.toNat < pointer.toNat → ¬ MWin statePad 200 w →
      ¬ MWin pad 136 w → ¬ MWin output 32 w → post.memory w = s.memory w) := by
  obtain ⟨capacity,bits,at2,next,tailPost,margin,capacitySmall,bitsLower,power,memory,globals,installed,domain,locals,
    ready,remaining,tailRun,finalClock,finalMemory,finalGlobals,finalDomain⟩ :=
    nodedb_body_constructor_returned_frame s post value total pointer code atTotal small atHeap aligned capped arena budget run
  obtain ⟨c,totalEq,capacityEq,geometry,stateEq,padEq,arrayEq,outputEq,tableEq,initialHeap,initial⟩ :=
    nodedb_constructor_loop_entry_workspace at2 next pointer capacity total array statePad pad output bits ready
      ((locals _ (by decide)).trans atTotal) ((locals _ (by decide)).trans atArray)
      (by rw [globals]; exact atState) (by rw [globals]; exact atPad) (by rw [globals]; exact atOutput)
      small capacitySmall margin outputAligned arrayEnd stateEnd padEnd outputEnd
      (by intro a al lo hi; rw [domain]; exact arena a al lo hi) (by
        intro j inside
        obtain ⟨src,len,sd,ld,sc,lc,bound⟩ := slices j inside
        exact ⟨src,len,by rw [domain]; exact sd,by rw [domain]; exact ld,
          by rw [memory]; exact sc,by rw [memory]; exact lc,bound⟩)
  obtain ⟨valueEq,middle,index,nextCount,nextHeap,indexTotal,loopRun,midInv,clockMid,memoryMid,globalsMid,domainMid,
    codeMid,tailDomain,wordFrame,heapGlobal,heapAligned,headerBelow,heapInside,stateGlobal,padGlobal,outputGlobal⟩ :=
    nodedb_suffix_returned_frame next tailPost value c geometry initialHeap initial
      (by rw [totalEq,capacityEq]; exact remaining) tailRun
  obtain ⟨tableLocal,keptLocals,nextCode,nextDomain,nextEndian,constructorMemory,heapRel,rest⟩ := ready
  have fullDomain : post.memaddrs = s.memaddrs :=
    finalDomain.symm.trans (tailDomain.trans (nextDomain.trans domain))
  have metadata := evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn_nodedb_build)
  rw [run] at metadata
  refine ⟨by rw [tableEq] at valueEq; exact valueEq,fullDomain,metadata.1,?_,?_,?_,?_,?_⟩
  · rw [← finalGlobals]
    simpa only [stateEq] using stateGlobal
  · rw [← finalGlobals]
    simpa only [padEq] using padGlobal
  · rw [← finalGlobals]
    simpa only [outputEq] using outputGlobal
  · refine ⟨nextHeap,?_,?_,heapAligned,heapInside,?_⟩
    · rw [← finalGlobals]; exact heapGlobal
    · rw [tableEq] at headerBelow; omega
    · intro a al lo hi
      rw [fullDomain]
      exact arena a al (by rw [tableEq] at headerBelow; omega) hi
  · intro w below outsideState outsidePad outsideOutput
    have protectedWord : NodedbProtected c w := by
      exact ⟨by rw [tableEq]; exact below,by rw [stateEq]; exact outsideState,
        by rw [padEq]; exact outsidePad,by rw [outputEq]; exact outsideOutput⟩
    exact (congrFun finalMemory.symm w).trans
      ((wordFrame w protectedWord).trans ((constructorMemory w below).trans (congrFun memory w)))

#print axioms nodedb_whole_body_returned_frame
end InitECandidate.Runtime
