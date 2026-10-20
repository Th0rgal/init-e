import InitECandidate.Runtime.MptNibbleUnsecuredTailBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptNibbleSecuredBranch : ProgHOL 64:=
 match structuralFunctionBody Guest.guestFn_mpt_nibble_key with | .seq (.ite _ branch _) _=>branch | _=>.skip

theorem source_mpt_nibble_key_branches : sourceFunctionBody Guest.guestFn_mpt_nibble_key=
 .seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "m"),.const 8])) (.const 0))
  mptNibbleSecuredBranch .skip) mptNibbleUnsecuredTail := by
 rw [sourceFunctionBody_eq_structural]
 rfl

/-- The complete actual key converter for an unsecured trie. Its real header
read either selects the unsecured path or rejects if inaccessible; there is
no readable-memory, successful allocation or callee-runtime premise. -/
theorem mpt_nibble_unsecured_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (table key length pointer : BitVec 64)
 (atTable : s.locals.lookup (ofString "m")=some (.val (.word table)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (unsecured : s.memory (table+8)=.word 0)
 (small : length.toNat+4<2^64) (code : s.code=originalRuntimeCode)
 (budget : 1+1+(length.toNat/4+4)≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_mpt_nibble_key) (1+1+(length.toNat/4+4)) := by
 have tail:=mpt_nibble_unsecured_tail_bounded s key length pointer atKey atLength atHeap small code budget
 rw [source_mpt_nibble_key_branches]
 unfold RunBounded at tail ⊢
 rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
 change s.memory (table+8#64)=.word (0#64) at unsecured
 by_cases readable : s.memaddrs (table+8#64)
 · have condition : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
     (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "m"),.const 8])) (.const 0))=some (.val (.word 0)) := by
     simp [evalHOLExact,evalListHOLExact,atTable,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,
      toExact,isWfShapeExactHOL,readable,unsecured,Compiler.Encoders.Asm.wordCmpHOL]
   rw [condition]
   simpa [evaluateHOLFiniteState_skip] using tail
 · have condition : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
     (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "m"),.const 8])) (.const 0))=none := by
     simp [evalHOLExact,evalListHOLExact,atTable,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,
      toExact,isWfShapeExactHOL,readable]
   rw [condition]
   simp
#print axioms source_mpt_nibble_key_branches
#print axioms mpt_nibble_unsecured_body_bounded
end InitECandidate.Runtime
