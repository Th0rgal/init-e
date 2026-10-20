import InitECandidate.Runtime.StateInitSuffixReturnedHeapFloor
import InitECandidate.Runtime.DecodeWitnessToMptReturnedHeapFloor
import InitECandidate.Runtime.StateInitWitnessCallBound
import InitECandidate.Runtime.PanReturnedPath
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem state_init_witness_call_returned_heap_floor {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length root emptyRoot : BitVec 64)
 (valid : WitnessTraversalEntryPrecondition layout (stateInitDbContext s layout.table) scratch heap pointer length)
 (atTable : s.locals.lookup (ofString "nodedb")=some (.val (.word layout.table)))
 (atRoot : s.locals.lookup (ofString "state_root")=some (.val (.word root)))
 (atEmpty : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
 (value : ValueHOL 64) (budget : decodeWitnessToMptSourceCeiling+399≤s.clock)
 (run : evaluateHOLFiniteState s (stateInitSpineDrop 4 (sourceFunctionBody Guest.guestFn_state_init))=(some (.returned value),post)) : StateInitHeapFloorReady layout.persistentFloor post := by
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
 obtain ⟨values,body,locals,shape,bodyValue,bodyPost,actualArgs,installed,bodyRun,resumed,inner,globals,code,_,_,tailRun,finalGlobals⟩ := decCall_returned run
 rw [args] at actualArgs
 cases Option.some.inj actualArgs
 rw [lookup] at installed
 obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj installed |>.symm
 have ready := decode_witness_to_mpt_returned_heap_floor layout entry bodyPost scratch heap pointer length root emptyRoot bodyValue
  entered atEnteredRoot atEmpty (by change decodeWitnessToMptSourceCeiling≤s.clock-1;omega) bodyRun
 have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_witness_to_mpt)
 rw [bodyRun] at metadata
 have resumedReady : StateInitHeapFloorReady layout.persistentFloor resumed := by
  obtain ⟨p,h,al,cap,lower⟩ := ready
  exact ⟨p,by rw [globals];exact h,al,cap,lower⟩
 have tailRel := normalRel_seq state_init_heap_floor_forward_preorder (state_init_heap_floor_forward_leaf
  (.store (.op .add [.var .global (ofString "ws"),.const 24]) (.var .local (ofString "root"))) rfl)
  (state_init_fixed_suffix_heap_floor_forward (floor:=layout.persistentFloor))
 have rel := normalRel_apply tailRel (X:=resumed)
  (by rw [tailRun];exact Or.inr (Or.inr (Or.inr ⟨value,rfl⟩))) (code.trans (metadata.1.trans valid.code))
 rw [tailRun] at rel
 obtain ⟨p,h,al,cap,lower⟩ := rel resumedReady
 exact ⟨p,by rw [finalGlobals];exact h,al,cap,lower⟩
#print axioms state_init_witness_call_returned_heap_floor
end InitECandidate.Runtime
