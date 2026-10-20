import InitECandidate.Runtime.StateInitStorageTableBodyMemory
import InitECandidate.Runtime.StateInitBlockTailReturnedMemory
import InitECandidate.Runtime.StateInitStorageTableTailBound
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem state_init_storage_tail_returned_memory {F : Type}(s post : PanSemStateFiniteExact 64 F)
 (heap ws : BitVec 64) (floor : Nat) (value : ValueHOL 64)
 (code : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (aligned : heap.toNat%8=0) (capped : heap.toNat≤33806089496) (heapFloor : floor≤heap.toNat)
 (atWs : s.globals.lookup (ofString "ws")=some (.val (.word ws)))
 (wsFloor : floor≤ws.toNat) (wsBound : ws.toNat+40≤33806089496)
 (domain : ∀a : BitVec 64,a.toNat<33806089496→s.memaddrs a)
 (run : evaluateHOLFiniteState s (stateInitSpineDrop 6 (sourceFunctionBody Guest.guestFn_state_init))=(some (.returned value),post)) :
 ∀watched : BitVec 64,watched.toNat<floor→post.memory watched=s.memory watched := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=(HolFiniteMapExact.empty.update (ofString "key_len",.val (.word (32#64)))).update
  (ofString "cap",.val (.word (64#64)))
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.const (32#64),.const (64#64)]=some [.val (.word (32#64)),.val (.word (64#64))] := by
  rw [evalListHOLFinite_eq_toExact];rfl
 have lookup:=htabNew_installed s 32 64 code
 rw [source_state_init_storage_table] at run
 obtain ⟨bodyValue,bodyPost,ready,output,bodyRun,locals,memory,globals,_,addrs,_,installed,tailRun,postEq⟩:=
  evaluate_decCall_returned_global_memory_clock_scope s post (ofString "t") (ofString "htab_new") .one .one _ _ _ _ callee value args lookup run
 obtain ⟨valueEq,rel,bodyMemory⟩:=state_init_storage_table_body_returned_memory (callEntryStateHOLFinite s callee) bodyPost heap bodyValue code
  (by simp (config:={decide:=true}) [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) atHeap aligned capped domain bodyRun
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_htab_new)
 rw [bodyRun] at metadata
 obtain ⟨newHeap,newAt,growth,newAligned,newCapped⟩:=rel.2 heap atHeap aligned capped
 let resumed:=setVarHOLFinite (ofString "t") bodyValue ready
 have resumedWs : resumed.globals.lookup (ofString "ws")=some (.val (.word ws)) := by
  change ready.globals.lookup _=_
  rw [globals,rel.1 _ (by decide)]
  exact atWs
 have resumedHeap : resumed.globals.lookup (ofString "heap_ptr")=some (.val (.word newHeap)) := by
  change ready.globals.lookup _=_;rw [globals];exact newAt
 obtain ⟨stored,storedRun,storedGlobals,storedCode,storedDomain,storeMemory⟩:=state_init_word_store_returned_reaches resumed output
  (.op .add [.var .global (ofString "ws"),.const 32]) (.var .local (ofString "t")) (ws+32) heap floor _ value
  (by simp [evalHOLExact,evalListHOLExact,resumedWs,wordOpHOL,wordOp,valueIsWord,valueWord])
  (by simp [resumed,setVarHOLFinite,valueEq,evalHOLExact,HolFiniteMapExact.lookup_update,FUPDATE])
  (by have natural : (ws+32).toNat=ws.toNat+32 := by
       rw [BitVec.toNat_add];change (ws.toNat+32)%(2^64)=ws.toNat+32;exact Nat.mod_eq_of_lt (by omega)
      rw [natural];omega) tailRun
 have resumedCode : resumed.code=originalRuntimeCode := installed.trans (metadata.1.trans code)
 have blockMemory:=state_init_block_tail_returned_memory stored output newHeap ws floor value
  (storedCode.trans resumedCode) (by rw [storedGlobals];exact resumedHeap) newAligned newCapped (by omega)
  (by rw [storedGlobals];exact resumedWs)
  (by intro a hi;rw [storedDomain];change ready.memaddrs a;rw [addrs,metadata.2.1];exact domain a hi) storedRun
 intro watched below
 rw [postEq,blockMemory watched below,storeMemory watched below]
 change ready.memory watched=s.memory watched
 rw [memory]
 exact bodyMemory watched (by omega)
#print axioms state_init_storage_tail_returned_memory
end InitECandidate.Runtime
