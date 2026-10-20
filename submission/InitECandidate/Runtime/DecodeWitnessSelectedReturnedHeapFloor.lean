import InitECandidate.Runtime.DecodeWitnessSelectedReturnedHeap
import InitECandidate.Runtime.WitnessDecoderReturnedHeapFloor
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
theorem decode_witness_selected_returned_heap_floor {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length found : BitVec 64) (value : ValueHOL 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (atResult : s.locals.lookup (ofString "r")=some (.rStruct [.val (.word found),.val (.word pointer),.val (.word length)]))
 (budget : witnessTraversalBodySourceCeiling+25≤s.clock)
 (run : evaluateHOLFiniteState s (decodeWitnessAt 4)=(some (.returned value),post)) : (∃nextHeap : BitVec 64,post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧nextHeap.toNat%8=0 ∧nextHeap.toNat≤33806089496 ∧layout.persistentFloor≤nextHeap.toNat) := by
 let callee := decodeWitnessBodyCallee layout.table pointer length
 let entry := callEntryStateHOLFinite s callee
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "db"),.rfield 1 (.var .local (ofString "r")),.rfield 2 (.var .local (ofString "r"))]=
  some [.val (.word layout.table),.val (.word pointer),.val (.word length)] := by
  rw [evalListHOLFinite_eq_toExact];simp [evalListHOLExact,evalHOLExact,valid.atDb,atResult]
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "_decode_witness_node")
  [.val (.word layout.table),.val (.word pointer),.val (.word length)]=
  some (sourceFunctionBody Guest.guestFn__decode_witness_node,callee,.one) := by
  rw [valid.code]
  exact pan_three_word_lookup _ _ _ _ _ _ layout.table pointer length (by decide) (by decide) (by decide)
   originalRuntimeCode_decodeWitness_lookup
 rw [source_decode_witness_selected_node] at run
 obtain ⟨values,body,locals,shape,bodyValue,bodyPost,actualArgs,installed,bodyRun,resumed,inner,globals,code,_,_,tailRun,finalGlobals⟩ := decCall_returned run
 rw [args] at actualArgs
 cases Option.some.inj actualArgs
 rw [lookup] at installed
 obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj installed |>.symm
 have entered := valid.with_locals_clock layout s scratch heap pointer length callee entry.clock
  (by simp (config:={decide:=true}) [callee,decodeWitnessBodyCallee,HolFiniteMapExact.lookup_update,FUPDATE])
 have ready := witness_decoder_returned_heap_floor layout entry bodyPost scratch heap pointer length bodyValue entered
  (by simp (config:={decide:=true}) [entry,callee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by change witnessTraversalBodySourceCeiling+6≤s.clock-1;omega) bodyRun
 have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn__decode_witness_node)
 rw [bodyRun] at metadata
 obtain ⟨oldHeap,oldAt,oldAligned,oldCapped,oldFloor⟩:=ready
 have resumedHeap : resumed.globals.lookup (ofString "heap_ptr")=some (.val (.word oldHeap)) := by rw [globals];exact oldAt
 have rel := normalRel_apply decode_witness_attach_hash_heap_relation (X:=resumed)
  (by rw [tailRun];exact Or.inr (Or.inr (Or.inr ⟨value,rfl⟩))) (code.trans (metadata.1.trans valid.code))
 rw [tailRun] at rel
 obtain ⟨p,h,growth,al,cap⟩:=rel.2 oldHeap resumedHeap oldAligned oldCapped
 exact ⟨p,by rw [finalGlobals];exact h,al,cap,by omega⟩
#print axioms decode_witness_selected_returned_heap_floor
end InitECandidate.Runtime
