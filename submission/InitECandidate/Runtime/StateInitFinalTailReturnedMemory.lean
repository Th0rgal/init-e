import InitECandidate.Runtime.StateInitGlobalAllocationNormalGeometry
import InitECandidate.Runtime.StateInitFinalTailBound
import InitECandidate.Runtime.StateInitHeapCallNormal
import InitECandidate.Runtime.AllocationFramedGlobals
import InitECandidate.Runtime.PanHandlerFreeCallControl
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem state_init_assignment_memory_all {F : Type} (s : PanSemStateFiniteExact 64 F) (kind : VarKind) (name : MlS) (expression : ExpHOL 64) :
 (evaluateHOLFiniteState s (.assign kind name expression)).2.memory=s.memory := by
 rw [evaluateHOLFiniteState_assign]
 repeat first | split | rfl
 all_goals cases kind <;> rfl

theorem state_init_return_memory_all {F : Type} (s : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) :
 (evaluateHOLFiniteState s (.return expression)).2.memory=s.memory := by
 rw [evaluateHOLFiniteState_return]
 repeat first | split | rfl

theorem state_init_seq_memory_all (first tail : ProgHOL 64)
 (a : ∀{F : Type}(s : PanSemStateFiniteExact 64 F),(evaluateHOLFiniteState s first).2.memory=s.memory)
 (b : ∀{F : Type}(s : PanSemStateFiniteExact 64 F),(evaluateHOLFiniteState s tail).2.memory=s.memory)
 {F : Type}(s : PanSemStateFiniteExact 64 F) : (evaluateHOLFiniteState s (.seq first tail)).2.memory=s.memory := by
 rw [evaluateHOLFiniteState_seq_line780]
 cases run : evaluateHOLFiniteState s first with
 | mk result post=>
  have frame:=a s
  rw [run] at frame
  cases result with
  | none=>exact (b post).trans frame
  | some _=>exact frame

theorem state_init_global_const_assignment_normal {F : Type}(s post : PanSemStateFiniteExact 64 F) (name : MlS) (word : BitVec 64)
 (run : evaluateHOLFiniteState s (.assign .global name (.const word))=(none,post)) : post=setGlobalHOLFinite name (.val (.word word)) s := by
 rw [evaluateHOLFiniteState_assign] at run
 simp only [evalHOLExact] at run
 split at run
 · exact (Prod.mk.inj run).2.symm
 · cases run

/-- Scratch-buffer and journal construction perform no memory writes at all
on an actual returned run, including the source global resets. -/
theorem state_init_final_tail_returned_memory {F : Type}(s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
 (code : s.code=originalRuntimeCode) (heapReady : StateInitHeapReady s)
 (run : evaluateHOLFiniteState s (stateInitSpineDrop 26 (sourceFunctionBody Guest.guestFn_state_init))=(some (.returned value),post)) :
 post.memory=s.memory := by
 obtain ⟨heap,atHeap,aligned,capped⟩:=heapReady
 rw [source_state_init_final_tail] at run
 obtain ⟨buffer,allocated,afterBuffer⟩:=seq_returned_of_nonreturning_first
  (evaluate_handlerFree_call_control s (some (.global,ofString "sk_buf")) (ofString "alloc") [.const 64]).2.2 run
 obtain ⟨bufferMem,bufferCode,_,_,_,bufferHeap,_,_,bufferAligned,bufferCapped⟩:=
  state_init_global_allocation_normal_geometry s buffer (ofString "sk_buf") (.const 64) heap 64
   (by rw [evalListHOLFinite_eq_toExact];rfl) code atHeap capped (by decide) allocated
 unfold stateInitJournalTail at afterBuffer
 obtain ⟨capacityState,capacityRun,afterCapacity⟩:=seq_returned_of_nonreturning_first
  (fun v=>evaluate_noDirectReturn _ rfl buffer v) afterBuffer
 have capacityEq:=state_init_global_const_assignment_normal buffer capacityState (ofString "journal_cap") 524288 capacityRun
 obtain ⟨journal,journalRun,resetRun⟩:=seq_returned_of_nonreturning_first
  (evaluate_handlerFree_call_control capacityState (some (.global,ofString "journal")) (ofString "alloc")
   [.panop .mul [.var .global (ofString "journal_cap"),.const 32]]).2.2 afterCapacity
 obtain ⟨journalMem,_,_,_,_,_,_,_,_,_⟩:=state_init_global_allocation_normal_geometry capacityState journal (ofString "journal")
  (.panop .mul [.var .global (ofString "journal_cap"),.const 32]) (allocationEnd heap 64) 16777216
  (by rw [evalListHOLFinite_eq_toExact];simp [capacityEq,evalListHOLExact,evalHOLExact,setGlobalHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,panOpHOL,valueIsWord,valueWord])
  (by rw [capacityEq];exact bufferCode.trans code)
  (by rw [capacityEq];simpa (config:={decide:=true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using bufferHeap)
  bufferCapped (by decide) journalRun
 have resetMemory : (evaluateHOLFiniteState journal
  (.seq (.assign .global (ofString "journal_n") (.const 0))
   (.seq (.assign .global (ofString "ts") (.const 0)) (.return (.const 0))))).2.memory=journal.memory := (state_init_seq_memory_all _ _ (fun st=>state_init_assignment_memory_all st _ _ _)
  (state_init_seq_memory_all _ _ (fun st=>state_init_assignment_memory_all st _ _ _) (fun st=>state_init_return_memory_all st _))) journal
 rw [resetRun] at resetMemory
 exact resetMemory.trans (journalMem.trans (by rw [capacityEq];exact bufferMem))
#print axioms state_init_assignment_memory_all
#print axioms state_init_return_memory_all
#print axioms state_init_seq_memory_all
#print axioms state_init_global_const_assignment_normal
#print axioms state_init_final_tail_returned_memory
end InitECandidate.Runtime
