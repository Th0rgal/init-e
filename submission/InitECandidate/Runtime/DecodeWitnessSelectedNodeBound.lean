import InitECandidate.Runtime.DecodeWitnessOuterTailBound
import InitECandidate.Runtime.DecodeWitnessFullContextPrefix
import InitECandidate.Runtime.WitnessTraversalEntryAfterRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem source_decode_witness_selected_node : decodeWitnessAt 4 =
 .decCall (ofString "nd") .one (ofString "_decode_witness_node")
 [.var .local (ofString "db"),.rfield 1 (.var .local (ofString "r")),.rfield 2 (.var .local (ofString "r"))]
 (decodeWitnessAt 5) := by
 unfold decodeWitnessAt sourceFunctionBody
 rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

/-- Actual selected database slice is decoded and its optional root hash attached;
all allocator rejection, exception, and access-error outcomes are included. -/
theorem runBounded_decode_witness_selected_node {F : Type} (layout : WitnessTraversalLayout)
 (s : PanSemStateFiniteExact 64 F) (scratch heap pointer length found : BitVec 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (atResult : s.locals.lookup (ofString "r")=some (.rStruct [.val (.word found),.val (.word pointer),.val (.word length)]))
 (budget : witnessTraversalBodySourceCeiling+25≤s.clock) :
 RunBounded s (decodeWitnessAt 4) (witnessTraversalBodySourceCeiling+25) := by
 let callee := decodeWitnessBodyCallee layout.table pointer length
 let entry := callEntryStateHOLFinite s callee
 have args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address))
   [.var .local (ofString "db"),.rfield 1 (.var .local (ofString "r")),.rfield 2 (.var .local (ofString "r"))] =
   some [.val (.word layout.table),.val (.word pointer),.val (.word length)] := by
  rw [evalListHOLFinite_eq_toExact]
  simp [evalListHOLExact,evalHOLExact,valid.atDb,atResult]
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "_decode_witness_node")
  [.val (.word layout.table),.val (.word pointer),.val (.word length)] =
  some (sourceFunctionBody Guest.guestFn__decode_witness_node,callee,.one) := by
  rw [valid.code]
  exact pan_three_word_lookup _ _ _ _ _ _ layout.table pointer length (by decide) (by decide) (by decide)
   originalRuntimeCode_decodeWitness_lookup
 have entered := valid.with_locals_clock layout s scratch heap pointer length callee entry.clock
  (by simp (config:={decide:=true}) [callee,decodeWitnessBodyCallee,HolFiniteMapExact.lookup_update,FUPDATE])
 change WitnessTraversalEntryPrecondition layout entry scratch heap pointer length at entered
 have body := runBounded_witness_decoder_uniform layout entry scratch heap pointer length entered
  (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,decodeWitnessBodyCallee,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callee,callEntryStateHOLFinite,decodeWitnessBodyCallee,HolFiniteMapExact.lookup_update,FUPDATE])
  (by change witnessTraversalBodySourceCeiling+6≤s.clock-1;omega)
 rw [source_decode_witness_selected_node]
 apply RunBounded.decCall (bodyCost:=witnessTraversalBodySourceCeiling+6) (tailCost:=18) args (by omega)
 intro actual actualLocals shape installed
 rw [lookup] at installed
 obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj installed |>.symm
 refine ⟨body,?_⟩
 intro value post run ticks
 have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn__decode_witness_node)
 rw [run] at metadata
 exact decode_witness_attach_hash_bounded _ (metadata.1.trans valid.code) ticks

#print axioms source_decode_witness_selected_node
#print axioms runBounded_decode_witness_selected_node
end InitECandidate.Runtime
