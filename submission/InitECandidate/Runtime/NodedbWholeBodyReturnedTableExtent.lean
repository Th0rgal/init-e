import InitECandidate.Runtime.NodedbConstructorLoopEntryExtent
import InitECandidate.Runtime.NodedbLoopHeapMonotone
import InitECandidate.Runtime.NodedbWholeBodyReturnedFrame
import InitECandidate.Runtime.NodedbBodyConstructorReturnedEndian
import InitECandidate.Runtime.HtabUnionSites
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem nodedb_whole_body_returned_table_extent {F : Type} (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
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
    ∃ keys stride capacity used values order orderPos count : BitVec 64, ∃ bits : Nat, ∃ finalHeap : BitVec 64,
      count.toNat ≤ total.toNat ∧ capacity.toNat ≤ 536870912 ∧ count.toNat < capacity.toNat ∧
      HtabAligned 32 pointer keys stride capacity used values order orderPos count bits post ∧
      OrderInv post capacity count used order orderPos ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      orderPos.toNat + capacity.toNat * 8 ≤ finalHeap.toNat := by
  obtain ⟨capacity,bits,at2,next,tailPost,margin,capacitySmall,bitsLower,power,memory,globals,installed,domain,endian,locals,
    ready,remaining,tailRun,finalClock,finalMemory,finalGlobals,finalDomain⟩ :=
    nodedb_body_constructor_returned_endian_frame s post value total pointer code atTotal small atHeap aligned capped arena budget run
  obtain ⟨c,totalEq,capacityEq,geometry,stateEq,padEq,arrayEq,outputEq,tableEq,initialHeap,initialExtent,initial⟩ :=
    nodedb_constructor_loop_entry_extent at2 next pointer capacity total array statePad pad output bits ready
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
  obtain ⟨monoIndex,monoCount,monoHeap,monoInv,heapMono⟩ :=
    nodedb_insertion_loop_heap_monotone c geometry
      (setVarHOLFinite (ofString "i") (.val (.word (0#64))) next) middle 0 initialHeap initial
      (by rw [totalEq,capacityEq]; exact remaining) loopRun
  have sameHeap : monoHeap = nextHeap :=
    HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (monoInv.heapGlobal.symm.trans midInv.heapGlobal)))
  rw [sameHeap] at heapMono
  obtain ⟨tableLocal,keptLocals,nextCode,nextDomain,nextEndian,constructorMemory,heapRel,rest⟩ := ready
  have memoryEq : post.memory = middle.memory := finalMemory.symm.trans memoryMid
  have domainEq : post.memaddrs = middle.memaddrs := finalDomain.symm.trans domainMid
  have wholeMeta := evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn_nodedb_build)
  rw [run] at wholeMeta
  have loopMeta := evaluateHOLFiniteState_metadata
    (setVarHOLFinite (ofString "i") (.val (.word (0#64))) next) nodedbInsertionLoop
  rw [loopRun] at loopMeta
  have middleEndian : middle.be = s.be := loopMeta.2.2.1.trans (nextEndian.trans endian)
  have endianEq : post.be = middle.be := wholeMeta.2.2.1.trans middleEndian.symm
  have codeEq : post.code = middle.code := by
    have midCode : middle.code = s.code := loopMeta.1.trans (nextCode.trans installed)
    exact wholeMeta.1.trans midCode.symm
  have room : nextCount.toNat ≤ c.capacity.toNat := by
    have occupied := midInv.occupancy
    have margin := geometry.capacityMargin
    rw [indexTotal] at occupied
    omega
  have inv := midInv.tableInv.congr domainEq endianEq codeEq
    (fun _ _ => congrFun memoryEq _) (fun _ _ => congrFun memoryEq _)
  have order := midInv.ordered.congr room domainEq endianEq
    (fun _ _ => congrFun memoryEq _) (fun _ _ => congrFun memoryEq _) (fun _ _ => congrFun memoryEq _)
  refine ⟨?_,c.keys,c.stride,c.capacity,c.used,c.values,c.order,c.orderPos,nextCount,c.bits,nextHeap,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [tableEq] using valueEq
  · have occupied := midInv.occupancy
    simpa only [indexTotal,totalEq] using occupied
  · simpa only [capacityEq] using geometry.capacitySmall
  · have occupied := midInv.occupancy
    have margin := geometry.capacityMargin
    rw [indexTotal] at occupied
    omega
  · simpa only [tableEq] using inv
  · exact order
  · rw [← finalGlobals]; exact heapGlobal
  · exact initialExtent.trans heapMono

#print axioms nodedb_whole_body_returned_table_extent
end InitECandidate.Runtime
