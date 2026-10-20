import InitECandidate.Runtime.MptNibbleUnsecuredTailBound
import InitECandidate.Runtime.HeapDeclarationReturnedContract
import InitECandidate.Runtime.KeyNibbleGlobalsFrame
import InitECandidate.Runtime.DiscardCallSuccessLocals
import InitECandidate.Runtime.EncodeHeaderReturnedPlan
import InitECandidate.Runtime.PanHandlerFreeCallControl
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual unsecured key converter returns its real newly allocated
buffer and exactly twice the input length. Its heap update and allocation
guards come from the same returned execution, without any fuel or room premise. -/
theorem mpt_nibble_unsecured_tail_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (key length pointer : BitVec 64) (value : ValueHOL 64)
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s mptNibbleUnsecuredTail=(some (.returned value),post)) :
 value=.rStruct [.val (.word pointer),.val (.word (2*length))] ∧
 post.globals=s.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer (2*length)))) ∧
 2*length≤(33806089496 : BitVec 64)-pointer ∧
 (allocationEnd pointer (2*length)).toNat≤33806089496 ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have metadata:=evaluateHOLFiniteState_metadata s mptNibbleUnsecuredTail
 rw [run] at metadata
 rw [source_mpt_nibble_unsecured_tail] at run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.panop .mul [.const 2,.var .local (ofString "klen")]]=some [.val (.word (2#64*length))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atLength,panOpHOL,valueIsWord,valueWord]
 obtain ⟨allocationPost,output,tailRun,scope,memory,domain,endian,installed,globals,request,finish⟩:=
  heap_declaration_returned_contract s post (ofString "nb2") _ _ pointer (2#64*length) value args atHeap code run
 let next:=setVarHOLFinite (ofString "nb2") (.val (.word pointer)) {allocationPost with locals:=s.locals}
 change evaluateHOLFiniteState next (.seq _ mptNibbleUnsecuredReturn)=(some (.returned value),output) at tailRun
 obtain ⟨converted,conversionRun,returnRun⟩:=encode_header_seq_returned_of_no_return next output _ _ value
  (fun v=>(evaluate_handlerFree_call_control next _ _ _).2.2 v) tailRun
 have locals:=evaluate_discard_call_success_locals next (ofString "key_to_nibbles")
  [.var .local (ofString "key"),.var .local (ofString "klen"),.var .local (ofString "nb2")]
  (by rw [conversionRun])
 rw [conversionRun] at locals
 have outputLocal : converted.locals.lookup (ofString "nb2")=some (.val (.word pointer)) := by
  rw [locals]
  simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have lengthLocal : converted.locals.lookup (ofString "klen")=some (.val (.word length)) := by
  rw [locals]
  simpa (config:={decide:=true}) [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atLength
 have expected : evaluateHOLFiniteState converted mptNibbleUnsecuredReturn=
  (some (.returned (.rStruct [.val (.word pointer),.val (.word (2#64*length))])),emptyLocalsHOLFinite converted) := by
  simp [mptNibbleUnsecuredReturn,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
   outputLocal,lengthLocal,panOpHOL,valueIsWord,valueWord,shapeOfHOLExact]
 obtain ⟨valueEq,outputEq⟩:=Prod.mk.inj (returnRun.symm.trans expected)
 have returned : value=.rStruct [.val (.word pointer),.val (.word (2#64*length))] :=
  PanSemResultExact.returned.inj (Option.some.inj valueEq)
 have conversionGlobals:=(key_nibble_call_globals_frame
  [.var .local (ofString "key"),.var .local (ofString "klen"),.var .local (ofString "nb2")]) next (installed.trans code)
 rw [conversionRun] at conversionGlobals
 refine ⟨returned,?_,request,finish,metadata.2.1,metadata.2.2.1,metadata.1⟩
 rw [scope,outputEq]
 exact conversionGlobals.trans globals

#print axioms mpt_nibble_unsecured_tail_returned_context
end InitECandidate.Runtime
