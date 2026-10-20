import InitECandidate.Runtime.WitnessDecoderReturnedHeap
import InitECandidate.Runtime.DecodeWitnessToMptUniformBound
import InitECandidate.Runtime.PanReturnedPath
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Optional final root-hash attachment preserves the actual aligned capped heap contract. -/
theorem decode_witness_attach_hash_heap_relation : NormalRel HeapRel (decodeWitnessAt 5) := by
 rw [source_decode_witness_attach_hash]
 have pre := heapRel_preorder
 apply normalRel_seq pre
 · unfold decodeWitnessAttachHash
   apply normalRel_ite pre
   · apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returnedRel
     exact normalRel_seq pre
      (normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_memcpy_lookup memcpy_returnedRel)
      (heapRel_leaf (fun _=>rfl))
   · exact heapRel_leaf (fun _=>rfl)
 · exact heapRel_leaf (fun _=>rfl)

/-- The selected actual decoder call and root-hash attachment return a real typed capped heap. -/
theorem decode_witness_selected_returned_heap {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length found : BitVec 64) (value : ValueHOL 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (atResult : s.locals.lookup (ofString "r")=some (.rStruct [.val (.word found),.val (.word pointer),.val (.word length)]))
 (budget : witnessTraversalBodySourceCeiling+25≤s.clock)
 (run : evaluateHOLFiniteState s (decodeWitnessAt 4)=(some (.returned value),post)) : StateInitHeapReady post := by
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
 have ready := witness_decoder_returned_heap layout entry bodyPost scratch heap pointer length bodyValue entered
  (by simp (config:={decide:=true}) [entry,callee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by change witnessTraversalBodySourceCeiling+6≤s.clock-1;omega) bodyRun
 have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn__decode_witness_node)
 rw [bodyRun] at metadata
 have resumedReady : StateInitHeapReady resumed := by
  obtain ⟨p,h,al,cap⟩ := ready
  exact ⟨p,by rw [globals];exact h,al,cap⟩
 have rel := normalRel_apply decode_witness_attach_hash_heap_relation (X:=resumed)
  (by rw [tailRun];exact Or.inr (Or.inr (Or.inr ⟨value,rfl⟩))) (code.trans (metadata.1.trans valid.code))
 rw [tailRun] at rel
 obtain ⟨p,h,al,cap⟩ := heapWord_of_rel rel resumedReady
 exact ⟨p,by rw [finalGlobals];exact h,al,cap⟩
#print axioms decode_witness_attach_hash_heap_relation
#print axioms decode_witness_selected_returned_heap
end InitECandidate.Runtime
