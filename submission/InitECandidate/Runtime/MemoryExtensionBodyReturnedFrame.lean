import InitECandidate.Runtime.MemoryExtensionChoiceReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Whole actual original extend_memory, including its zero early return and
three real declarations. Actual helper-derived expansion size and concrete
physical buffer ownership suffice; allocator room and callee executions are
never assumed. -/
theorem memory_extension_body_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame base length capacity expansion pointer scratch : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atExpansion : s.locals.lookup (ofString "expand_by")=some (.val (.word expansion)))
 (headerDomain : ∀offset∈([24,32,40] : List (BitVec 64)),s.memaddrs (frame+offset))
 (baseAt : s.memory (frame+24)=.word base) (lengthAt : s.memory (frame+32)=.word length)
 (capacityAt : s.memory (frame+40)=.word capacity)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : length.toNat≤capacity.toNat) (expansionBound : expansion.toNat<2^38)
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat) (ordered : pointer.toNat≤scratch.toNat)
 (belowFrame : scratch.toNat≤frame.toNat) (frameExtent : frame.toNat+280≤33806089496)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_extend_memory)=(some (.returned value),post)) :
 value=.val (.word (0#64)) ∧
 ∃newCapacity nextPointer : BitVec 64,
 post.memory (frame+24)=.word base ∧post.memory (frame+32)=.word (length+expansion) ∧post.memory (frame+40)=.word newCapacity ∧
 (length+expansion).toNat≤newCapacity.toNat ∧base.toNat+newCapacity.toNat≤nextPointer.toNat ∧
 pointer.toNat≤nextPointer.toNat ∧nextPointer.toNat≤scratch.toNat ∧
 post.globals.lookup (ofString "ev")=some (.val (.word frame)) ∧
 post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
 post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word nextPointer)) ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat → watched≠frame+32 → watched≠frame+40 → post.memory watched=s.memory watched) ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (memoryExtensionAt 0)=_ at run
 by_cases zero : expansion=0#64
 · have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .equal (.var .local (ofString "expand_by")) (.const 0))=some (.val (.word 1)) := by
    simp [evalHOLExact,atExpansion,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
   have direct : evaluateHOLFiniteState s (memoryExtensionAt 0)=
    (some (.returned (.val (.word (0#64)))),emptyLocalsHOLFinite s) := by
    rw [source_memory_extension_0,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,cmp]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
   obtain ⟨returned,postEq⟩:=Prod.mk.inj (run.symm.trans direct)
   refine ⟨PanSemResultExact.returned.inj (Option.some.inj returned),capacity,pointer,?_,?_,?_,?_,oldExtent,by omega,ordered,?_,?_,?_,?_,?_,?_,?_⟩
   all_goals try rw [postEq]
   · exact baseAt
   · simpa [zero,emptyLocalsHOLFinite] using lengthAt
   · exact capacityAt
   · simpa [zero] using lengthOrder
   · exact atFrame
   · exact atScratch
   · exact atPointer
   · intros;rfl
   all_goals rfl
 · have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .equal (.var .local (ofString "expand_by")) (.const 0))=some (.val (.word 0)) := by
    simp [evalHOLExact,atExpansion,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
   rw [source_memory_extension_0,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,cmp] at run
   simp only [if_pos rfl,evaluateHOLFiniteState_skip] at run
   change evaluateHOLFiniteState s (memoryExtensionAt 1)=_ at run
   rw [source_memory_extension_1] at run
   obtain ⟨loadedLength,firstOutput,lengthEval,firstRun,firstScope⟩:=funding_declaration_returned_context run
   have loadLength:=eval_fundingLoad s frame (32#64) length atFrame (headerDomain 32 (by simp)) lengthAt
   have lengthEq : loadedLength=.val (.word length):=Option.some.inj (lengthEval.symm.trans loadLength)
   subst loadedLength
   let first:=setVarHOLFinite (ofString "len") (.val (.word length)) s
   change evaluateHOLFiniteState first (memoryExtensionAt 2)=_ at firstRun
   rw [source_memory_extension_2] at firstRun
   obtain ⟨loadedCapacity,secondOutput,capacityEval,secondRun,secondScope⟩:=funding_declaration_returned_context firstRun
   have loadCapacity:=eval_fundingLoad first frame (40#64) capacity atFrame (headerDomain 40 (by simp)) capacityAt
   have capacityEq : loadedCapacity=.val (.word capacity):=Option.some.inj (capacityEval.symm.trans loadCapacity)
   subst loadedCapacity
   let second:=setVarHOLFinite (ofString "cap") (.val (.word capacity)) first
   change evaluateHOLFiniteState second (memoryExtensionAt 3)=_ at secondRun
   rw [source_memory_extension_3] at secondRun
   obtain ⟨newLength,thirdOutput,newLengthEval,thirdRun,thirdScope⟩:=funding_declaration_returned_context secondRun
   have sumEval : @evalHOLExact 64 F _ second.toExact (fun a=>Classical.propDecidable (second.memaddrs a))
    (.op .add [.var .local (ofString "len"),.var .local (ofString "expand_by")])=some (.val (.word (length+expansion))) := by
    simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,atExpansion,wordOpHOL,wordOp,valueIsWord,valueWord]
   have sumEq : newLength=.val (.word (length+expansion)):=Option.some.inj (newLengthEval.symm.trans sumEval)
   subst newLength
   let third:=setVarHOLFinite (ofString "nlen") (.val (.word (length+expansion))) second
   change evaluateHOLFiniteState third (memoryExtensionAt 4)=_ at thirdRun
   have len : third.locals.lookup (ofString "len")=some (.val (.word length)) := by
    simp (config:={decide:=true}) [third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   have cap : third.locals.lookup (ofString "cap")=some (.val (.word capacity)) := by
    simp (config:={decide:=true}) [third,second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   have exp : third.locals.lookup (ofString "expand_by")=some (.val (.word expansion)) := by
    simpa (config:={decide:=true}) [third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atExpansion
   have nlen : third.locals.lookup (ofString "nlen")=some (.val (.word (length+expansion))) := by
    simp [third,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   have nonwrap:=memory_extension_length_nonwrap length capacity expansion lengthOrder (by omega) expansionBound
   have result:=memory_extension_choice_returned third thirdOutput frame base length capacity expansion (length+expansion) pointer scratch value atFrame len cap exp nlen (headerDomain 24 (by simp)) baseAt capacityAt atPointer atScratch lengthOrder nonwrap.1 expansionBound oldExtent ordered belowFrame frameExtent code thirdRun
   rw [firstScope,secondScope,thirdScope]
   exact result
#print axioms memory_extension_body_returned_frame
end InitECandidate.Runtime
