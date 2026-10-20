import InitECandidate.Runtime.MemoryExtensionChoiceRuntimeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Whole original extend_memory has a fixed concrete source bound under its
physical EVM vector ownership and real cost-helper expansion ceiling. Failed
allocations/accesses and zero early return are included, with no success premise. -/
theorem memory_extension_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame base length capacity expansion pointer scratch : BitVec 64)
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
 (code : s.code=originalRuntimeCode) (budget : memoryExtensionBodyCost≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_extend_memory) memoryExtensionBodyCost := by
 rw [sourceFunctionBody_eq_structural]
 change RunBounded s (memoryExtensionAt 0) _
 rw [source_memory_extension_0]
 have guard : RunBounded s (.ite (.cmp .equal (.var .local (ofString "expand_by")) (.const 0)) (.return (.const 0)) .skip) 0 :=
  RunBounded.ofProg (ProgBounded.straight _ (by decide_cbv)) code (by omega)
 have result:=RunBounded.seq guard (tail:=memoryExtensionAt 1) (b:=memoryExtensionBodyCost) (by simpa only [Nat.zero_add] using budget) (by
  intro next ran installed remaining
  rcases ite_normal_cases s next _ _ _ ran with returned|skipped
  · simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact] at returned
  · rw [evaluateHOLFiniteState_skip] at skipped
    have equal : next=s:=(Prod.mk.inj skipped).2.symm
    subst next
    rw [source_memory_extension_1]
    have loadedLength:=eval_fundingLoad s frame (32#64) length atFrame (headerDomain 32 (by simp)) lengthAt
    apply RunBounded.decWord s _ _ length loadedLength
    let first:=setVarHOLFinite (ofString "len") (.val (.word length)) s
    change RunBounded first (memoryExtensionAt 2) _
    rw [source_memory_extension_2]
    have loadedCapacity:=eval_fundingLoad first frame (40#64) capacity atFrame (headerDomain 40 (by simp)) capacityAt
    apply RunBounded.decWord first _ _ capacity loadedCapacity
    let second:=setVarHOLFinite (ofString "cap") (.val (.word capacity)) first
    change RunBounded second (memoryExtensionAt 3) _
    have lengthLocal : second.locals.lookup (ofString "len")=some (.val (.word length)) := by
     simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have expansionLocal : second.locals.lookup (ofString "expand_by")=some (.val (.word expansion)) := by
     simpa (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atExpansion
    have sumEval : @evalHOLExact 64 F _ second.toExact (fun a=>Classical.propDecidable (second.memaddrs a))
     (.op .add [.var .local (ofString "len"),.var .local (ofString "expand_by")])=some (.val (.word (length+expansion))) := by
     simp [evalHOLExact,evalListHOLExact,lengthLocal,expansionLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    rw [source_memory_extension_3]
    apply RunBounded.decWord second _ _ (length+expansion) sumEval
    let third:=setVarHOLFinite (ofString "nlen") (.val (.word (length+expansion))) second
    change RunBounded third (memoryExtensionAt 4) _
    have len : third.locals.lookup (ofString "len")=some (.val (.word length)) := by
     simp (config:={decide:=true}) [third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have cap : third.locals.lookup (ofString "cap")=some (.val (.word capacity)) := by
     simp (config:={decide:=true}) [third,second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have exp : third.locals.lookup (ofString "expand_by")=some (.val (.word expansion)) := by
     simpa (config:={decide:=true}) [third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atExpansion
    have nlen : third.locals.lookup (ofString "nlen")=some (.val (.word (length+expansion))) := by
     simp [third,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have nonwrap:=memory_extension_length_nonwrap length capacity expansion lengthOrder (by omega) expansionBound
    exact memory_extension_choice_bounded third frame base length capacity expansion (length+expansion) pointer scratch atFrame len cap exp nlen (headerDomain 24 (by simp)) baseAt atPointer atScratch lengthOrder nonwrap.1 expansionBound oldExtent ordered belowFrame frameExtent code remaining)
 simpa only [Nat.zero_add] using result
#print axioms memory_extension_body_bounded
end InitECandidate.Runtime
