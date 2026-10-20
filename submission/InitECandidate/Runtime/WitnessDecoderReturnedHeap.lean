import InitECandidate.Runtime.WitnessMptWrapperReturnedHeap
import InitECandidate.Runtime.ScratchReleaseSuccessful
import InitECandidate.Runtime.ScratchMarkDeclarationExact
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem decoder_initializers_scoped {F : Type} (s : PanSemStateFiniteExact 64 F)
 (scratch : BitVec 64) (code : s.code=originalRuntimeCode)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch))) (ticks : s.clock≠0) :
 Scoped (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_witness_node))
 (evaluateHOLFiniteState (setVarHOLFinite (ofString "nd") (.val (.word (0#64)))
  (setVarHOLFinite (ofString "e") (.val (.word (0#64)))
  (setVarHOLFinite (ofString "mark") (.val (.word scratch)) {s with clock:=s.clock-1}))) decodeWitnessAfterLocals) := by
 rw [source_decode_witness_body,evaluate_scratch_mark_declaration_exact s scratch code atScratch ticks]
 apply scoped_trans (scoped_restore _ _)
 rw [source_decode_witness_after_mark,evaluateHOLFiniteState_dec_total]
 simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
 apply scoped_trans (scoped_restore _ _)
 rw [evaluateHOLFiniteState_dec_total]
 simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
 exact scoped_restore _ _

/-- The complete original scratch-cleanup wrapper returns an actual aligned capped heap. -/
theorem witness_decoder_returned_heap {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64) (value : ValueHOL 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (budget : witnessTraversalBodySourceCeiling+6≤s.clock)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_witness_node)=(some (.returned value),post)) :
 StateInitHeapReady post := by
 let entered := setVarHOLFinite (ofString "nd") (.val (.word (0#64)))
  (setVarHOLFinite (ofString "e") (.val (.word (0#64)))
  (setVarHOLFinite (ofString "mark") (.val (.word scratch)) {s with clock:=s.clock-1}))
 let callee := decodeWitnessMptCallee layout.table pointer length scratch
 let entry := callEntryStateHOLFinite entered callee
 have agreement := decoder_initializers_scoped s scratch valid.code valid.atScratch (by omega)
 rw [run] at agreement
 let output := (evaluateHOLFiniteState entered decodeWitnessAfterLocals).2
 have inner : evaluateHOLFiniteState entered decodeWitnessAfterLocals=(some (.returned value),output) :=
  Prod.ext agreement.1.symm rfl
 have args : evalListHOLFinite entered (h:=fun a=>Classical.propDecidable (entered.memaddrs a))
  [.var .local (ofString "db"),.var .local (ofString "p"),.var .local (ofString "n"),.var .local (ofString "mark")]=
  some [.val (.word layout.table),.val (.word pointer),.val (.word length),.val (.word scratch)] := by
  rw [evalListHOLFinite_eq_toExact]
  simp (config:={decide:=true}) [evalListHOLExact,evalHOLExact,entered,setVarHOLFinite,
   HolFiniteMapExact.lookup_update,FUPDATE,valid.atDb,atPointer,atLength]
 have lookup : lookupCodeHOLFinite entered.code.lookup (ofString "_decode_witness_node_mpt")
  [.val (.word layout.table),.val (.word pointer),.val (.word length),.val (.word scratch)]=
  some (sourceFunctionBody Guest.guestFn__decode_witness_node_mpt,callee,.one) := by
  exact pan_four_word_shape_lookup entered.code.lookup (ofString "_decode_witness_node_mpt")
   (ofString "db") (ofString "p") (ofString "n") (ofString "mark")
   (sourceFunctionBody Guest.guestFn__decode_witness_node_mpt) .one layout.table pointer length scratch
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
   (by change s.code.lookup _=_;rw [valid.code];exact originalRuntimeCode_decodeWitnessMpt_lookup)
 have handlerNoReturn (current : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
  (evaluateHOLFiniteState current decodeWitnessRlpHandler).1≠some (.returned v) :=
  evaluate_noDirectReturn _ (by rw [source_decode_witness_rlp_handler];rfl) current v
 have handlerTerminal (current : PanSemStateFiniteExact 64 F) :
  (evaluateHOLFiniteState current decodeWitnessRlpHandler).1≠none := by
  rw [source_decode_witness_rlp_handler]
  apply evaluate_seq_terminal
  intro next
  rw [evaluateHOLFiniteState_raise]
  dsimp only
  repeat' split <;> simp_all
 have callNoReturn (v : ValueHOL 64) :
  (evaluateHOLFiniteState entered (.call (some (some (.local,ofString "nd"),
   some (ofString "RlpErr",ofString "e",decodeWitnessRlpHandler))) (ofString "_decode_witness_node_mpt")
   [.var .local (ofString "db"),.var .local (ofString "p"),.var .local (ofString "n"),.var .local (ofString "mark")])).1≠some (.returned v) := by
  intro returned
  apply evaluate_localCall_handler_no_return entered _ (ofString "nd") (ofString "_decode_witness_node_mpt")
   .one _ _ _ decodeWitnessRlpHandler (ofString "RlpErr") (ofString "e") callee args lookup v
   (fun current=>handlerNoReturn current v)
  exact Prod.ext returned rfl
 rw [source_decode_witness_after_locals] at inner
 obtain ⟨middle,called,returned⟩ := seq_returned_of_nonreturning_first callNoReturn inner
 have unhandled := evaluate_localCall_terminal_handler_normal_result entered middle (ofString "nd")
  (ofString "_decode_witness_node_mpt") .one _ _ _ decodeWitnessRlpHandler (ofString "RlpErr") (ofString "e")
  callee args lookup handlerTerminal called
 obtain ⟨bodyValue,bodyPost,bodyRun,memory,globals,_,_,codeMiddle,_,other⟩ := assign_call_normal entered middle (ofString "nd")
  (ofString "_decode_witness_node_mpt") _ _ _ callee .one args lookup unhandled
 have entryValid := valid.with_locals_clock layout s scratch heap pointer length callee entry.clock
  (by simp (config:={decide:=true}) [callee,decodeWitnessMptCallee,decodeWitnessBodyCallee,HolFiniteMapExact.lookup_update,FUPDATE])
 change WitnessTraversalEntryPrecondition layout entry scratch heap pointer length at entryValid
 have ready := witness_mpt_wrapper_returned_heap layout entry bodyPost scratch heap pointer length bodyValue entryValid
  (by simp (config:={decide:=true}) [entry,callee,decodeWitnessMptCallee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp (config:={decide:=true}) [entry,callee,decodeWitnessMptCallee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by change witnessTraversalBodySourceCeiling+2≤s.clock-1-1;omega) bodyRun
 have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn__decode_witness_node_mpt)
 rw [bodyRun] at metadata
 have code : middle.code=originalRuntimeCode := codeMiddle.trans (metadata.1.trans valid.code)
 have atMark : middle.locals.lookup (ofString "mark")=some (.val (.word scratch)) := by
  rw [other _ (by decide)]
  simp (config:={decide:=true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 rw [source_decode_witness_cleanup] at returned
 obtain ⟨released,releaseRun,returnRun⟩ := seq_returned_of_nonreturning_first
  (evaluate_handlerFree_call_control middle none (ofString "scratch_release") [.var .local (ofString "mark")]).2.2 returned
 have releaseGlobals := (scratchRelease_normal_globals middle released (.var .local (ofString "mark")) scratch
  (by rw [evalListHOLFinite_eq_toExact];simp [evalListHOLExact,evalHOLExact,atMark]) code releaseRun).1
 have finalGlobals := return_local_globals released output (ofString "nd") value returnRun
 obtain ⟨nextHeap,atHeap,aligned,capped⟩ := ready
 refine ⟨nextHeap,?_,aligned,capped⟩
 rw [agreement.2.2.2.1,finalGlobals,releaseGlobals]
 simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using globals ▸ atHeap
#print axioms witness_decoder_returned_heap
end InitECandidate.Runtime
