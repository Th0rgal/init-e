import InitECandidate.Runtime.WitnessTraversalBodyMemoryFrame
import InitECandidate.Runtime.WitnessTraversalWrapperUniformBound
import InitECandidate.Runtime.PanLocalCallTerminalHandlerNormal
import InitECandidate.Runtime.PanLocalCallHandlerNoReturn
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem mpt_wrapper_initializers_scoped {F : Type} (s : PanSemStateFiniteExact 64 F) :
 Scoped (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_witness_node_mpt))
 (evaluateHOLFiniteState (setVarHOLFinite (ofString "nd") (.val (.word (0#64)))
  (setVarHOLFinite (ofString "e") (.val (.word (0#64))) s)) decodeWitnessMptAfterLocals) := by
 rw [source_decode_witness_mpt_body,evaluateHOLFiniteState_dec_total]
 simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
 apply scoped_trans (scoped_restore _ _)
 rw [evaluateHOLFiniteState_dec_total]
 simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
 exact scoped_restore _ _

/-- Actual MptErr wrapper normal-return heap contract, derived from the real traversal body. -/
theorem witness_mpt_wrapper_returned_memory {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64) (value : ValueHOL 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (budget : witnessTraversalBodySourceCeiling+2≤s.clock)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_witness_node_mpt)=(some (.returned value),post)) :
 ∀watched : BitVec 64,layout.databaseCeiling≤watched.toNat→watched.toNat<layout.dbHeap.toNat→post.memory watched=s.memory watched := by
 let entered := setVarHOLFinite (ofString "nd") (.val (.word (0#64)))
  (setVarHOLFinite (ofString "e") (.val (.word (0#64))) s)
 let callee := decodeWitnessBodyCallee layout.table pointer length
 let entry := callEntryStateHOLFinite entered callee
 have agreement := mpt_wrapper_initializers_scoped s
 rw [run] at agreement
 let output := (evaluateHOLFiniteState entered decodeWitnessMptAfterLocals).2
 have inner : evaluateHOLFiniteState entered decodeWitnessMptAfterLocals=(some (.returned value),output) :=
  Prod.ext agreement.1.symm rfl
 have args : evalListHOLFinite entered (h:=fun a=>Classical.propDecidable (entered.memaddrs a))
  [.var .local (ofString "db"),.var .local (ofString "p"),.var .local (ofString "n")]=
  some [.val (.word layout.table),.val (.word pointer),.val (.word length)] := by
  rw [evalListHOLFinite_eq_toExact]
  simp (config:={decide:=true}) [evalListHOLExact,evalHOLExact,entered,setVarHOLFinite,
   HolFiniteMapExact.lookup_update,FUPDATE,valid.atDb,atPointer,atLength]
 have lookup : lookupCodeHOLFinite entered.code.lookup (ofString "_decode_witness_node_body")
  [.val (.word layout.table),.val (.word pointer),.val (.word length)]=
  some (sourceFunctionBody Guest.guestFn__decode_witness_node_body,callee,.one) := by
  rw [show entered.code=originalRuntimeCode from valid.code]
  exact pan_three_word_lookup _ _ _ _ _ _ layout.table pointer length (by decide) (by decide) (by decide)
   originalRuntimeCode_decodeWitnessBody_lookup
 have handlerNoReturn (current : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
  (evaluateHOLFiniteState current decodeWitnessMptHandler).1≠some (.returned v) := by
  exact evaluate_noDirectReturn _ (by rw [source_decode_witness_mpt_handler];rfl) current v
 have handlerTerminal (current : PanSemStateFiniteExact 64 F) :
  (evaluateHOLFiniteState current decodeWitnessMptHandler).1≠none := by
  rw [source_decode_witness_mpt_handler]
  apply evaluate_seq_terminal
  intro next
  rw [evaluateHOLFiniteState_raise]
  dsimp only
  repeat' split <;> simp_all
 have callNoReturn (v : ValueHOL 64) :
  (evaluateHOLFiniteState entered (.call (some (some (.local,ofString "nd"),
   some (ofString "MptErr",ofString "e",decodeWitnessMptHandler))) (ofString "_decode_witness_node_body")
   [.var .local (ofString "db"),.var .local (ofString "p"),.var .local (ofString "n")])).1≠some (.returned v) := by
  intro returned
  apply evaluate_localCall_handler_no_return entered _ (ofString "nd") (ofString "_decode_witness_node_body")
   .one _ _ _ decodeWitnessMptHandler (ofString "MptErr") (ofString "e") callee args lookup v
   (fun current=>handlerNoReturn current v)
  exact Prod.ext returned rfl
 rw [source_decode_witness_mpt_after_locals] at inner
 obtain ⟨middle,called,returned⟩ := seq_returned_of_nonreturning_first callNoReturn inner
 have unhandled := evaluate_localCall_terminal_handler_normal_result entered middle (ofString "nd")
  (ofString "_decode_witness_node_body") .one _ _ _ decodeWitnessMptHandler (ofString "MptErr") (ofString "e")
  callee args lookup handlerTerminal called
 obtain ⟨bodyValue,bodyPost,bodyRun,memory,globals,_,_,_,_,_⟩ := assign_call_normal entered middle (ofString "nd")
  (ofString "_decode_witness_node_body") _ _ _ callee .one args lookup unhandled
 have entryValid := valid.with_locals_clock layout s scratch heap pointer length callee entry.clock
  (by simp (config:={decide:=true}) [callee,decodeWitnessBodyCallee,HolFiniteMapExact.lookup_update,FUPDATE])
 change WitnessTraversalEntryPrecondition layout entry scratch heap pointer length at entryValid
 have small := witnessTraversalLoopCost_mono layout.inputLimit 134217712 valid.inputLimitBound
 have frame := witness_traversal_body_returned_memory layout entry bodyPost scratch heap pointer length bodyValue entryValid
  (by simp (config:={decide:=true}) [entry,callee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by change witnessTraversalLoopCost layout.inputLimit≤s.clock-1;change _≤witnessTraversalBodySourceCeiling at small;omega) bodyRun
 have finalMemory:=return_local_memory_frame middle output (ofString "nd") value returned
 rw [agreement.2.2.1,finalMemory,memory]
 exact frame
#print axioms witness_mpt_wrapper_returned_memory
end InitECandidate.Runtime
