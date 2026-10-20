import InitECandidate.Runtime.StateInitStorageTableTailBound
import InitECandidate.Runtime.DecodeWitnessToMptReturnedHeap
import InitECandidate.Runtime.OriginalDecodeWitnessToMptCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Context-only renaming for expressing geometric DB obligations in state_init. -/
def stateInitDbContext {F : Type} (s : PanSemStateFiniteExact 64 F) (table : BitVec 64) : PanSemStateFiniteExact 64 F :=
 {s with locals:=s.locals.update (ofString "db",.val (.word table))}

theorem source_state_init_witness_call : stateInitSpineDrop 4 (sourceFunctionBody Guest.guestFn_state_init)=
 .decCall (ofString "root") .one (ofString "decode_witness_to_mpt")
 [.var .local (ofString "nodedb"),.var .local (ofString "state_root")]
 (.seq (.store (.op .add [.var .global (ofString "ws"),.const 24]) (.var .local (ofString "root")))
 (stateInitSpineDrop 6 (sourceFunctionBody Guest.guestFn_state_init))) := by
 unfold sourceFunctionBody
 rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

/-- Actual root-decoder declaration and all remaining original constructors. -/
theorem runBounded_state_init_witness_call {F : Type} (layout : WitnessTraversalLayout)
 (s : PanSemStateFiniteExact 64 F) (scratch heap pointer length root emptyRoot : BitVec 64)
 (valid : WitnessTraversalEntryPrecondition layout (stateInitDbContext s layout.table) scratch heap pointer length)
 (atTable : s.locals.lookup (ofString "nodedb")=some (.val (.word layout.table)))
 (atRoot : s.locals.lookup (ofString "state_root")=some (.val (.word root)))
 (atEmpty : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
 (budget : decodeWitnessToMptSourceCeiling+399≤s.clock) :
 RunBounded s (stateInitSpineDrop 4 (sourceFunctionBody Guest.guestFn_state_init)) (decodeWitnessToMptSourceCeiling+399) := by
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
 have body := runBounded_decode_witness_to_mpt_uniform layout entry scratch heap pointer length root emptyRoot entered atEnteredRoot atEmpty
  (by change decodeWitnessToMptSourceCeiling≤s.clock-1;omega)
 rw [source_state_init_witness_call]
 apply RunBounded.decCall (bodyCost:=decodeWitnessToMptSourceCeiling) (tailCost:=398) args (by omega)
 intro actual actualLocals shape installed
 rw [lookup] at installed
 obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj installed |>.symm
 refine ⟨body,?_⟩
 intro value post run ticks
 have ready := decode_witness_to_mpt_returned_heap layout entry post scratch heap pointer length root emptyRoot value
  entered atEnteredRoot atEmpty (by change decodeWitnessToMptSourceCeiling≤s.clock-1;omega) run
 have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_witness_to_mpt)
 rw [run] at metadata
 exact state_init_store_seq_bounded _ _ state_init_storage_table_tail_bounded _ (metadata.1.trans valid.code) ready ticks
#print axioms source_state_init_witness_call
#print axioms runBounded_state_init_witness_call
end InitECandidate.Runtime
