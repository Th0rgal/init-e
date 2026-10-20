import InitECandidate.Runtime.StateInitBlockTailBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Real declared table constructor preserves the checked heap frontier for its actual continuation. -/
theorem state_init_table_declaration_bounded (name : MlS) (width capacity : BitVec 64)
 {tail : ProgHOL 64} {cost : Nat} (bounded : StateInitHeapBounded tail cost) :
 StateInitHeapBounded (.decCall name .one (ofString "htab_new") [.const width,.const capacity] tail)
 (htabNewCost capacity+1+cost) := by
 intro F s code heap budget
 obtain ⟨pointer,atHeap,aligned,capped⟩ := heap
 let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word width))).update (ofString "cap",.val (.word capacity))
 let entry := callEntryStateHOLFinite s callee
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.const width,.const capacity]=
  some [.val (.word width),.val (.word capacity)] := by rw [evalListHOLFinite_eq_toExact];rfl
 have lookup := htabNew_installed s width capacity code
 have body := evaluate_htabNew_body_bounded entry width capacity pointer code
  (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  atHeap aligned capped (by change htabNewCost capacity≤s.clock-1;omega)
 apply RunBounded.decCall (bodyCost:=htabNewCost capacity) (tailCost:=cost) args budget
 intro actual actualLocals shape installed
 rw [lookup] at installed
 obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj installed |>.symm
 refine ⟨body,?_⟩
 intro value post run ticks
 have rel := normalRel_apply htabNew_normalRel (X:=entry)
  (by rw [run];exact Or.inr (Or.inr (Or.inr ⟨value,rfl⟩))) code
 rw [run] at rel
 have nextHeap : StateInitHeapReady (setVarHOLFinite name value {post with locals:=s.locals}) :=
  heapWord_of_rel rel ⟨pointer,atHeap,aligned,capped⟩
 have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_new)
 rw [run] at metadata
 exact bounded _ (metadata.1.trans code) nextHeap ticks

theorem source_state_init_storage_table : stateInitSpineDrop 6 (sourceFunctionBody Guest.guestFn_state_init) =
 .decCall (ofString "t") .one (ofString "htab_new") [.const 32,.const 64]
 (.seq (.store (.op .add [.var .global (ofString "ws"),.const 32]) (.var .local (ofString "t")))
 (stateInitSpineDrop 8 (sourceFunctionBody Guest.guestFn_state_init))) := by
 unfold sourceFunctionBody
 rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl
/-- All eight state tables and remaining block/scratch/journal allocations, no reserve assumption. -/
theorem state_init_storage_table_tail_bounded : StateInitHeapBounded
 (stateInitSpineDrop 6 (sourceFunctionBody Guest.guestFn_state_init)) 398 := by
 rw [source_state_init_storage_table]
 intro F s code heap budget
 have stored : StateInitHeapBounded (.seq
  (.store (.op .add [.var .global (ofString "ws"),.const 32]) (.var .local (ofString "t")))
  (stateInitSpineDrop 8 (sourceFunctionBody Guest.guestFn_state_init))) 364 := by
  intro F s code heap budget
  exact state_init_store_seq_bounded _ _ state_init_block_tail_bounded s code heap budget
 exact state_init_table_declaration_bounded (ofString "t") 32 64 stored s code heap budget
#print axioms state_init_table_declaration_bounded
#print axioms source_state_init_storage_table
#print axioms state_init_storage_table_tail_bounded
end InitECandidate.Runtime
