import InitECandidate.Runtime.StateInitTableNormalMemoryUnfuelled
import InitECandidate.Runtime.WordStoreNormalMemory
import InitECandidate.Runtime.PanHandlerFreeCallControl
import InitECandidate.Runtime.AllocationFramedGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem state_init_table_list_returned_frame_reaches {F : Type} (tables : List (Nat×Nat×Nat))
 (tail : ProgHOL 64) (s post : PanSemStateFiniteExact 64 F) (heap bs : BitVec 64) (floor : Nat) (value : ValueHOL 64)
 (plan : BlockPlan tables) (code : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (aligned : heap.toNat%8=0) (capped : heap.toNat≤33806089496) (heapFloor : floor≤heap.toNat)
 (atBs : s.globals.lookup (ofString "bs")=some (.val (.word bs)))
 (bsFloor : floor≤bs.toNat) (bsBound : bs.toNat+80≤33806089496)
 (domain : ∀a : BitVec 64,a.toNat<33806089496→s.memaddrs a)
 (run : evaluateHOLFiniteState s (blockCtorSeq tables tail)=(some (.returned value),post)) :
 ∃ready : PanSemStateFiniteExact 64 F,evaluateHOLFiniteState ready tail=(some (.returned value),post) ∧
 ready.code=s.code ∧ready.memaddrs=s.memaddrs ∧HeapRel s.globals ready.globals ∧
 (∀watched : BitVec 64,watched.toNat<floor→ ready.memory watched=s.memory watched) := by
 induction tables generalizing s heap with
 | nil=>exact ⟨s,run,rfl,rfl,heapRel_preorder.refl _,fun _ _=>rfl⟩
 | cons spec rest ih=>
  obtain ⟨width,capacity,offset⟩:=spec
  obtain ⟨widthBound,capacityBound,⟨bits,power⟩,offsetBound,_,restPlan⟩:=plan
  unfold blockCtorSeq at run
  obtain ⟨called,callRun,afterCall⟩:=seq_returned_of_nonreturning_first
   (evaluate_handlerFree_call_control s (some (.local,ofString "t")) (ofString "htab_new") _).2.2 run
  obtain ⟨atT,rel,callMemory⟩:=state_init_table_normal_memory_unfuelled s called (ofString "t")
   (BitVec.ofNat 64 width) (BitVec.ofNat 64 capacity) heap bits code atHeap aligned capped domain
   (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt capacityBound];exact power)
   (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : width<2^64)];omega) callRun
  have calledMetadata:=evaluateHOLFiniteState_metadata s (.call (some (some (.local,ofString "t"),none)) (ofString "htab_new")
   [.const (BitVec.ofNat 64 width),.const (BitVec.ofNat 64 capacity)])
  rw [callRun] at calledMetadata
  obtain ⟨newHeap,newHeapAt,growth,newAligned,newCapped⟩:=rel.2 heap atHeap aligned capped
  obtain ⟨stored,storeRun,tailRun⟩:=seq_returned_of_first (evaluate_store_control_frame called _ _).1 afterCall
  have bsCalled : called.globals.lookup (ofString "bs")=some (.val (.word bs)) := by rw [rel.1 _ (by decide)];exact atBs
  have storeMemory:=evaluate_word_store_normal_memory called stored _ _ (bs+BitVec.ofNat 64 offset) heap
   (by simp [blockPointerStore,evalHOLExact,evalListHOLExact,bsCalled,wordOpHOL,wordOp,valueIsWord,valueWord])
   (by simp [blockPointerStore,evalHOLExact,atT]) storeRun
  have storeRunOpaque : evaluateHOLFiniteState called (blockPointerStore offset)=(none,stored) := storeRun
  have storeGlobals : stored.globals=called.globals := by
   have all : (evaluateHOLFiniteState called (blockPointerStore offset)).2.globals=called.globals := by
    unfold blockPointerStore
    rw [evaluateHOLFiniteState_store]
    repeat first | split | rfl
   rw [storeRunOpaque] at all
   exact all
  have storedMetadata:=evaluateHOLFiniteState_metadata called (blockPointerStore offset)
  rw [storeRunOpaque] at storedMetadata
  obtain ⟨ready,reached,readyCode,readyDomain,readyRel,readyMemory⟩:=ih stored newHeap restPlan
   (storedMetadata.1.trans (calledMetadata.1.trans code)) (by rw [storeGlobals];exact newHeapAt) newAligned newCapped
   (by omega) (by rw [storeGlobals];exact bsCalled) (by intro a hi;rw [storedMetadata.2.1,calledMetadata.2.1];exact domain a hi) tailRun
  refine ⟨ready,reached,readyCode.trans (storedMetadata.1.trans calledMetadata.1),
   readyDomain.trans (storedMetadata.2.1.trans calledMetadata.2.1),?_,?_⟩
  · apply heapRel_preorder.trans _ stored.globals _ ?_ readyRel
    rw [storeGlobals];exact rel
  · intro watched below
    rw [readyMemory watched below,storeMemory.2 watched ?_,callMemory watched (by omega)]
    intro equal
    have natural : (bs+BitVec.ofNat 64 offset).toNat=bs.toNat+offset := by
     rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : offset<2^64),Nat.mod_eq_of_lt (by omega : bs.toNat+offset<2^64)]
    have same:=congrArg BitVec.toNat equal
    rw [natural] at same
    omega
#print axioms state_init_table_list_returned_frame_reaches
end InitECandidate.Runtime
