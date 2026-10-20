import InitECandidate.Runtime.WitnessDecoderReturnedMemory
import InitECandidate.Runtime.WitnessDecoderReturnedNode
import InitECandidate.Runtime.WitnessDecoderReturnedHeapFloor
import InitECandidate.Runtime.DecodeWitnessSelectedReturnedHeap
import InitECandidate.Runtime.DecodeWitnessAttachHashMemoryFrame
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
theorem decode_witness_selected_returned_node {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length found root : BitVec 64) (value : ValueHOL 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (atResult : s.locals.lookup (ofString "r")=some (.rStruct [.val (.word found),.val (.word pointer),.val (.word length)]))
 (atRoot : s.locals.lookup (ofString "root_hash")=some (.val (.word root)))
 (budget : witnessTraversalBodySourceCeiling+25≤s.clock)
 (run : evaluateHOLFiniteState s (decodeWitnessAt 4)=(some (.returned value),post)) : ∃node : BitVec 64,value=.val (.word node) ∧(node=0 ∨(layout.persistentFloor≤node.toNat ∧node.toNat+32≤33806089496)) := by
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
 obtain ⟨bodyValue,bodyPost,ready,output,bodyRun,locals,memory,globals,clock,_,_,code,tailRun,postEq⟩:=
  evaluate_decCall_returned_global_memory_clock_scope s post (ofString "nd") (ofString "_decode_witness_node") .one .one
   _ _ _ _ callee value args lookup run
 have entered:=valid.with_locals_clock layout s scratch heap pointer length callee entry.clock
  (by simp (config:={decide:=true}) [callee,decodeWitnessBodyCallee,HolFiniteMapExact.lookup_update,FUPDATE])
 change WitnessTraversalEntryPrecondition layout entry scratch heap pointer length at entered
 have atP : entry.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
  simp (config:={decide:=true}) [entry,callee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atN : entry.locals.lookup (ofString "n")=some (.val (.word length)) := by
  simp [entry,callee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have bodyBudget : witnessTraversalBodySourceCeiling+6≤entry.clock := by change _≤s.clock-1;omega
 obtain ⟨node,nodeValue,nodeEnvelope⟩:=witness_decoder_returned_node layout entry bodyPost scratch heap pointer length bodyValue entered atP atN bodyBudget bodyRun
 let resumed:=setVarHOLFinite (ofString "nd") bodyValue ready
 have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn__decode_witness_node)
 rw [bodyRun] at metadata
 have atResumedNode : resumed.locals.lookup (ofString "nd")=some (.val (.word node)) := by
  simp [resumed,setVarHOLFinite,nodeValue,HolFiniteMapExact.lookup_update,FUPDATE]
 rw [source_decode_witness_attach_hash] at tailRun
 obtain ⟨attached,attachRun,returnRun⟩:=seq_returned_of_nonreturning_first
  (fun v=>evaluate_noDirectReturn decodeWitnessAttachHash (by unfold decodeWitnessAttachHash;decide) resumed v) tailRun
 have kept:=evaluate_avoidsLocal_flowing (ofString "nd") decodeWitnessAttachHash
  (by unfold decodeWitnessAttachHash;decide) resumed (by rw [attachRun];exact Or.inl rfl)
 rw [attachRun] at kept
 have atAttached : attached.locals.lookup (ofString "nd")=some (.val (.word node)) := kept.trans atResumedNode
 exact ⟨node,return_local_word attached output (ofString "nd") node value atAttached returnRun,nodeEnvelope⟩
#print axioms decode_witness_selected_returned_node
end InitECandidate.Runtime
