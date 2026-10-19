import InitECandidate.Runtime.NodedbEmptyConstructorLoopEntryExtent
import InitECandidate.Runtime.NodedbEmptyWholeBodyReturnedFrame
import InitECandidate.Runtime.NodedbBodyConstructorReturnedEndian
import InitECandidate.Runtime.HtabUnionSites
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem nodedb_empty_whole_body_returned_table_extent {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) (total pointer : BitVec 64)
    (array statePad pad output : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word total)))
    (empty : total = 0)
    (atArray : s.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 →
      s.memaddrs a)
    (budget : nodedbBodyCost total ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_nodedb_build) =
      (some (.returned value),post)) :
    value = .val (.word pointer) ∧
    ∃ keys stride capacity used values order orderPos count : BitVec 64, ∃ bits : Nat, ∃ finalHeap : BitVec 64,
      count.toNat ≤ total.toNat ∧ capacity.toNat ≤ 536870912 ∧
      HtabAligned 32 pointer keys stride capacity used values order orderPos count bits post ∧
      OrderInv post capacity count used order orderPos ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      orderPos.toNat + capacity.toNat * 8 ≤ finalHeap.toNat := by
  have small : total.toNat ≤ 134217712 := by rw [empty]; simp
  obtain ⟨capacity,bits,at2,next,tailPost,margin,capacitySmall,bitsLower,power,memory,globals,installed,
    domain,endian,locals,ready,clock,returned,tailClock,tailMemory,tailGlobals,tailDomain⟩ :=
    nodedb_body_constructor_returned_endian_frame s post value total pointer code atTotal small atHeap aligned capped
      arena budget run
  have atTotal2 : at2.locals.lookup (ofString "n") = some (.val (.word total)) :=
    (locals _ (by decide)).trans atTotal
  have atArray2 : at2.locals.lookup (ofString "slice_arr") = some (.val (.word array)) :=
    (locals _ (by decide)).trans atArray
  have atState2 : at2.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) := by
    rw [globals]; exact atState
  have atPad2 : at2.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
    rw [globals]; exact atPad
  have atOutput2 : at2.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) := by
    rw [globals]; exact atOutput
  have arena2 : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat →
      a.toNat < 33806089496 → at2.memaddrs a := by
    intro a al lo hi
    rw [domain]
    exact arena a al lo hi
  obtain ⟨c,totalZero,capacityAt,tableAt,pointerAt,padAt,arrayAt,outputAt,heap,initialExtent,entry⟩ :=
    nodedb_empty_constructor_loop_entry_extent at2 next pointer capacity total array statePad pad output bits
      ready atTotal2 atArray2 atState2 atPad2 atOutput2 empty arena2
  obtain ⟨valueEq,loopRun,clockEq,memoryEq,globalsEq,domainEq,codeEq,heapGlobal,heapAligned,heapInside,
    stateGlobal,padGlobal,outputGlobal⟩ :=
    nodedb_empty_declared_suffix_returned_frame next tailPost value c heap totalZero entry returned
  have metadata := evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn_nodedb_build)
  rw [run] at metadata
  obtain ⟨_,_,nextCode,nextDomain,nextEndian,rest⟩ := ready
  have memoryPost : post.memory = next.memory := tailMemory.symm.trans memoryEq
  have domainPost : post.memaddrs = next.memaddrs := tailDomain.symm.trans domainEq
  have endianPost : post.be = next.be := metadata.2.2.1.trans (nextEndian.trans endian).symm
  have codePost : post.code = next.code := metadata.1.trans (nextCode.trans installed).symm
  have inv := entry.tableInv.congr domainPost endianPost codePost
    (fun _ _ => congrFun memoryPost _) (fun _ _ => congrFun memoryPost _)
  have ordered := entry.ordered.congr (by simp) domainPost endianPost
    (fun _ _ => congrFun memoryPost _) (fun _ _ => congrFun memoryPost _) (fun _ _ => congrFun memoryPost _)
  refine ⟨?_,c.keys,c.stride,c.capacity,c.used,c.values,c.order,c.orderPos,0,c.bits,heap,?_,?_,?_,ordered,?_,initialExtent⟩
  · simpa only [tableAt] using valueEq
  · simp
  · simpa only [capacityAt] using capacitySmall
  · simpa only [tableAt] using inv
  · rw [← tailGlobals]; exact heapGlobal

#print axioms nodedb_empty_whole_body_returned_table_extent
end InitECandidate.Runtime
