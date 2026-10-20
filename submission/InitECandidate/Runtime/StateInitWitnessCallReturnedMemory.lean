import InitECandidate.Runtime.StateInitStorageTailReturnedMemory
import InitECandidate.Runtime.StateInitWitnessCallBound
import InitECandidate.Runtime.DecodeWitnessToMptReturnedMemory
import InitECandidate.Runtime.DecodeWitnessToMptReturnedNode
import InitECandidate.Runtime.DecodeWitnessToMptReturnedHeapFloor
import InitECandidate.Runtime.WitnessInitializerWsGlobalClosure
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
theorem state_init_witness_call_returned_memory {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length root emptyRoot ws : BitVec 64)
 (valid : WitnessTraversalEntryPrecondition layout (stateInitDbContext s layout.table) scratch heap pointer length)
 (atTable : s.locals.lookup (ofString "nodedb")=some (.val (.word layout.table)))
 (atRoot : s.locals.lookup (ofString "state_root")=some (.val (.word root)))
 (atEmpty : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
 (atWs : s.globals.lookup (ofString "ws")=some (.val (.word ws)))
 (wsFloor : layout.dbHeap.toNat≤ws.toNat) (wsBound : ws.toNat+40≤33806089496)
 (domain : ∀a : BitVec 64,a.toNat<33806089496→s.memaddrs a)
 (value : ValueHOL 64) (budget : decodeWitnessToMptSourceCeiling+399≤s.clock)
 (run : evaluateHOLFiniteState s (stateInitSpineDrop 4 (sourceFunctionBody Guest.guestFn_state_init))=(some (.returned value),post)) :
 ∀watched : BitVec 64,layout.databaseCeiling≤watched.toNat→watched.toNat<layout.dbHeap.toNat→post.memory watched=s.memory watched := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64) := (HolFiniteMapExact.empty.update (ofString "db",.val (.word layout.table))).update
  (ofString "root_hash",.val (.word root))
 let entry := callEntryStateHOLFinite s callee
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "nodedb"),.var .local (ofString "state_root")]=some [.val (.word layout.table),.val (.word root)] := by
  rw [evalListHOLFinite_eq_toExact];simp [evalListHOLExact,evalHOLExact,atTable,atRoot]
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "decode_witness_to_mpt")
  [.val (.word layout.table),.val (.word root)]=some (sourceFunctionBody Guest.guestFn_decode_witness_to_mpt,callee,.one) := by
  rw [show s.code=originalRuntimeCode from valid.code]
  exact pan_two_word_lookup _ _ _ _ _ layout.table root (by decide) originalRuntimeCode_decodeWitnessToMpt_lookup
 have entered := valid.with_locals_clock layout (stateInitDbContext s layout.table) scratch heap pointer length callee entry.clock
  (by simp (config:={decide:=true}) [callee,HolFiniteMapExact.lookup_update,FUPDATE])
 change WitnessTraversalEntryPrecondition layout entry scratch heap pointer length at entered
 have atEnteredRoot : entry.locals.lookup (ofString "root_hash")=some (.val (.word root)) := by
  simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 rw [source_state_init_witness_call] at run
 obtain ⟨bodyValue,bodyPost,ready,output,bodyRun,locals,memory,globals,_,addrs,_,installed,tailRun,postEq⟩:=
  evaluate_decCall_returned_global_memory_clock_scope s post (ofString "root") (ofString "decode_witness_to_mpt") .one .one _ _ _ _ callee value args lookup run
 have rootBudget : decodeWitnessToMptSourceCeiling≤entry.clock := by change _≤s.clock-1;omega
 have rootFrame:=decode_witness_to_mpt_returned_memory layout entry bodyPost scratch heap pointer length root emptyRoot bodyValue
  entered atEnteredRoot atEmpty rootBudget bodyRun
 obtain ⟨node,nodeValue,_⟩:=decode_witness_to_mpt_returned_node layout entry bodyPost scratch heap pointer length root emptyRoot bodyValue
  entered atEnteredRoot atEmpty rootBudget bodyRun
 obtain ⟨newHeap,newAt,newAligned,newCapped,newFloor⟩:=decode_witness_to_mpt_returned_heap_floor layout entry bodyPost scratch heap pointer length root emptyRoot bodyValue
  entered atEnteredRoot atEmpty rootBudget bodyRun
 have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_witness_to_mpt)
 rw [bodyRun] at metadata
 have wsKept:=evaluate_witness_initializer_ws_global entry (sourceFunctionBody Guest.guestFn_decode_witness_to_mpt)
  (ofString "ws") (by simp [witnessInitializerWatchedGlobals])
  (witness_initializer_ws_global_installed originalRuntimeCode_decodeWitnessToMpt_lookup (by decide) (by simp [witnessInitializerWatchedGlobals])) valid.code
 rw [bodyRun] at wsKept
 let resumed:=setVarHOLFinite (ofString "root") bodyValue ready
 have resumedWs : resumed.globals.lookup (ofString "ws")=some (.val (.word ws)) := by
  change ready.globals.lookup _=_
  rw [globals,wsKept]
  exact atWs
 obtain ⟨stored,storedRun,storedGlobals,storedCode,storedDomain,storeFrame⟩:=state_init_word_store_returned_reaches resumed output
  (.op .add [.var .global (ofString "ws"),.const 24]) (.var .local (ofString "root")) (ws+24) node layout.dbHeap.toNat _ value
  (by simp [evalHOLExact,evalListHOLExact,resumedWs,wordOpHOL,wordOp,valueIsWord,valueWord])
  (by simp [resumed,setVarHOLFinite,nodeValue,evalHOLExact,HolFiniteMapExact.lookup_update,FUPDATE])
  (by have natural : (ws+24).toNat=ws.toNat+24 := by
       rw [BitVec.toNat_add];change (ws.toNat+24)%(2^64)=ws.toNat+24;exact Nat.mod_eq_of_lt (by omega)
      rw [natural];omega) tailRun
 have storedHeap : stored.globals.lookup (ofString "heap_ptr")=some (.val (.word newHeap)) := by
  rw [storedGlobals];change ready.globals.lookup _=_;rw [globals];exact newAt
 have storedWs : stored.globals.lookup (ofString "ws")=some (.val (.word ws)) := by rw [storedGlobals];exact resumedWs
 have dbFloor:=valid.dbHeapBeforeFloor
 have suffixFrame:=state_init_storage_tail_returned_memory stored output newHeap ws layout.dbHeap.toNat value
  (storedCode.trans (installed.trans (metadata.1.trans valid.code))) storedHeap newAligned newCapped (by omega) storedWs wsFloor wsBound
  (by intro a hi;rw [storedDomain];change ready.memaddrs a;rw [addrs,metadata.2.1];exact domain a hi) storedRun
 intro watched lo hi
 rw [postEq,suffixFrame watched hi,storeFrame watched hi]
 change ready.memory watched=s.memory watched
 rw [memory]
 exact rootFrame watched lo hi
#print axioms state_init_witness_call_returned_memory
end InitECandidate.Runtime
