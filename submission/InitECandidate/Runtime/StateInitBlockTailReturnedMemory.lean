import InitECandidate.Runtime.StateInitTableListReturnedMemory
import InitECandidate.Runtime.StateInitWordStoreReturnedMemory
import InitECandidate.Runtime.StateInitFinalTailReturnedMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem state_init_block_tail_returned_memory {F : Type}(s post : PanSemStateFiniteExact 64 F)
 (heap ws : BitVec 64) (floor : Nat) (value : ValueHOL 64)
 (code : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (aligned : heap.toNat%8=0) (capped : heap.toNat≤33806089496) (heapFloor : floor≤heap.toNat)
 (atWs : s.globals.lookup (ofString "ws")=some (.val (.word ws)))
 (domain : ∀a : BitVec 64,a.toNat<33806089496→s.memaddrs a)
 (run : evaluateHOLFiniteState s (stateInitSpineDrop 8 (sourceFunctionBody Guest.guestFn_state_init))=(some (.returned value),post)) :
 ∀watched : BitVec 64,watched.toNat<floor→post.memory watched=s.memory watched := by
 rw [source_stateInit_block] at run
 unfold blockSegment at run
 obtain ⟨block,blockRun,afterBlock⟩:=seq_returned_of_nonreturning_first
  (evaluate_handlerFree_call_control s (some (.global,ofString "bs")) (ofString "alloc") [.const 80]).2.2 run
 obtain ⟨blockMemory,blockCode,blockDomain,_,blockAt,blockHeap,others,blockCovers,blockAligned,blockCapped⟩:=
  state_init_global_allocation_normal_geometry s block (ofString "bs") (.const 80) heap 80
   (by rw [evalListHOLFinite_eq_toExact];rfl) code atHeap capped (by decide) blockRun
 have blockBound : heap.toNat+80≤33806089496 := by change heap.toNat+80≤_ at blockCovers;omega
 have wsBlock : block.globals.lookup (ofString "ws")=some (.val (.word ws)) := by rw [others _ (by decide) (by decide)];exact atWs
 obtain ⟨start,startRun,startGlobals,startCode,startDomain,startMemory⟩:=state_init_word_store_returned_reaches block post
  (.op .add [.var .global (ofString "bs"),.const 0]) (.var .global (ofString "ws")) heap ws floor _ value
  (by simpa [evalHOLExact,evalListHOLExact,blockAt,wordOpHOL,wordOp,valueIsWord,valueWord])
  (by simpa [evalHOLExact,wsBlock]) heapFloor afterBlock
 have startHeap : start.globals.lookup (ofString "heap_ptr")=some (.val (.word (allocationEnd heap 80))) := by rw [startGlobals];exact blockHeap
 have startBs : start.globals.lookup (ofString "bs")=some (.val (.word heap)) := by rw [startGlobals];exact blockAt
 obtain ⟨first,firstRun,firstCode,firstDomain,firstRel,firstMemory⟩:=state_init_table_list_returned_frame_reaches blockTablesFirst _ start post
  (allocationEnd heap 80) heap floor value blockPlan_first (startCode.trans (blockCode.trans code)) startHeap blockAligned blockCapped
  (by have h:=blockCovers;change heap.toNat+80≤_ at h;omega) startBs heapFloor blockBound
  (by intro a hi;rw [startDomain,blockDomain];exact domain a hi) startRun
 have firstBs : first.globals.lookup (ofString "bs")=some (.val (.word heap)) := by rw [firstRel.1 _ (by decide)];exact startBs
 have globalWord (offset : Nat) (small : offset≤72) : (heap+BitVec.ofNat 64 offset).toNat=heap.toNat+offset := by
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : offset<2^64),Nat.mod_eq_of_lt (by omega : heap.toNat+offset<2^64)]
 obtain ⟨zero56,zero56Run,zero56Globals,zero56Code,zero56Domain,zero56Memory⟩:=state_init_word_store_returned_reaches first post
  (.op .add [.var .global (ofString "bs"),.const 56]) (.const 0) (heap+56) 0 floor _ value
  (by simp [evalHOLExact,evalListHOLExact,firstBs,wordOpHOL,wordOp,valueIsWord,valueWord]) rfl
  (by have natural:=globalWord 56 (by decide);change (heap+56).toNat=heap.toNat+56 at natural;rw [natural];omega) firstRun
 have zero56Bs : zero56.globals.lookup (ofString "bs")=some (.val (.word heap)) := by rw [zero56Globals];exact firstBs
 obtain ⟨zero64,zero64Run,zero64Globals,zero64Code,zero64Domain,zero64Memory⟩:=state_init_word_store_returned_reaches zero56 post
  (.op .add [.var .global (ofString "bs"),.const 64]) (.const 0) (heap+64) 0 floor _ value
  (by simp [evalHOLExact,evalListHOLExact,zero56Bs,wordOpHOL,wordOp,valueIsWord,valueWord]) rfl
  (by have natural:=globalWord 64 (by decide);change (heap+64).toNat=heap.toNat+64 at natural;rw [natural];omega) zero56Run
 obtain ⟨secondHeap,secondAt,growth,secondAligned,secondCapped⟩:=firstRel.2 (allocationEnd heap 80) startHeap blockAligned blockCapped
 have secondHeapAt : zero64.globals.lookup (ofString "heap_ptr")=some (.val (.word secondHeap)) := by rw [zero64Globals,zero56Globals];exact secondAt
 obtain ⟨last,lastRun,lastCode,lastDomain,lastRel,lastMemory⟩:=state_init_table_list_returned_frame_reaches blockTablesLast _ zero64 post
  secondHeap heap floor value blockPlan_last (zero64Code.trans (zero56Code.trans (firstCode.trans (startCode.trans (blockCode.trans code)))))
  secondHeapAt secondAligned secondCapped (by have h:=blockCovers;change heap.toNat+80≤_ at h;omega)
  (by rw [zero64Globals,zero56Globals];exact firstBs) heapFloor blockBound
  (by intro a hi;rw [zero64Domain,zero56Domain,firstDomain,startDomain,blockDomain];exact domain a hi) zero64Run
 have finalReady:=heapWord_of_rel lastRel ⟨secondHeap,secondHeapAt,secondAligned,secondCapped⟩
 have codeLast : last.code=originalRuntimeCode := by
  rw [lastCode,zero64Code,zero56Code,firstCode,startCode,blockCode];exact code
 have finalMemory:=state_init_final_tail_returned_memory last post value codeLast finalReady lastRun
 intro watched below
 rw [finalMemory,lastMemory watched below,zero64Memory watched below,zero56Memory watched below,
  firstMemory watched below,startMemory watched below,blockMemory]
#print axioms state_init_block_tail_returned_memory
end InitECandidate.Runtime
