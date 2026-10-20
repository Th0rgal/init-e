import InitECandidate.Runtime.MptNibbleUnsecuredReturnedContext
import InitECandidate.Runtime.MptNibbleUnsecuredBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The whole original unsecured converter returns the actual allocated
buffer and exact doubled length. The header read is taken from the same run;
an inaccessible header cannot satisfy the returned-execution premise. -/
theorem mpt_nibble_unsecured_body_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (table key length pointer : BitVec 64) (value : ValueHOL 64)
 (atTable : s.locals.lookup (ofString "m")=some (.val (.word table)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (unsecured : s.memory (table+8)=.word 0) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_mpt_nibble_key)=(some (.returned value),post)) :
 value=.rStruct [.val (.word pointer),.val (.word (2*length))] ∧
 post.globals=s.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer (2*length)))) ∧
 2*length≤(33806089496 : BitVec 64)-pointer ∧
 (allocationEnd pointer (2*length)).toNat≤33806089496 ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 rw [source_mpt_nibble_key_branches,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at run
 change s.memory (table+8#64)=.word (0#64) at unsecured
 by_cases readable : s.memaddrs (table+8#64)
 · have condition : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
     (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "m"),.const 8])) (.const 0))=some (.val (.word 0)) := by
     simp [evalHOLExact,evalListHOLExact,atTable,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,
      toExact,isWfShapeExactHOL,readable,unsecured,Compiler.Encoders.Asm.wordCmpHOL]
   rw [condition] at run
   exact mpt_nibble_unsecured_tail_returned_context s post key length pointer value atKey atLength atHeap code
    (by simpa [evaluateHOLFiniteState_skip] using run)
 · have condition : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
     (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "m"),.const 8])) (.const 0))=none := by
     simp [evalHOLExact,evalListHOLExact,atTable,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,
      toExact,isWfShapeExactHOL,readable]
   rw [condition] at run
   cases run

#print axioms mpt_nibble_unsecured_body_returned
end InitECandidate.Runtime
