import InitECandidate.Runtime.EvmOperandStackGrowthReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Full original stack_push body in the actual full-capacity case, including
both header-load declarations and their real returned scopes. -/
theorem stack_push_growing_body_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame oldBase index scratch frontier a b c d watched : BitVec 64) (value : ValueHOL 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atValue : s.locals.lookup (ofString "v")=some (fundingU256 a b c d))
 (headerDomain : ∀offset∈([8,16,232] : List (BitVec 64)),s.memaddrs (frame+offset))
 (baseAt : s.memory (frame+8)=.word oldBase) (indexAt : s.memory (frame+16)=.word index)
 (capacityAt : s.memory (frame+232)=.word index) (positive : 1≤index.toNat)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrontier : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)))
 (ordered : frontier≤scratch) (scratchBeforeFrame : scratch.toNat≤frame.toNat)
 (frameExtent : frame.toNat+280≤33806089496) (scratchCap : scratch.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (above : scratch.toNat≤watched.toNat) (differentBase : watched≠frame+8)
 (differentCounter : watched≠frame+16) (differentCapacity : watched≠frame+232)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (stackPushAt 0)=(some (.returned value),post)) :
 let grown:=stackPushGrownCapacity index
 let fresh:=scratchAllocationEnd scratch (grown*32#64)
 value=.val (.word 0) ∧post.memory watched=s.memory watched ∧
 post.memory (frame+16)=.word (index+1) ∧
 post.memory (frame+8)=.word fresh ∧post.memory (frame+232)=.word grown ∧
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word fresh)) ∧
 frontier.toNat≤fresh.toNat ∧fresh.toNat+grown.toNat*32≤scratch.toNat ∧
 index.toNat+1≤grown.toNat ∧grown.toNat≤1024 ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 rw [source_stack_push_0] at run
 obtain ⟨indexValue,firstOutput,indexEval,firstRun,firstScope⟩:=funding_declaration_returned_context run
 have loadedIndex:=eval_fundingLoad s frame (16#64) index atCurrent (headerDomain 16 (by simp)) indexAt
 have indexEq : indexValue=.val (.word index):=Option.some.inj (indexEval.symm.trans loadedIndex)
 subst indexValue
 let first:=setVarHOLFinite (ofString "sp") (.val (.word index)) s
 change evaluateHOLFiniteState first (stackPushAt 1)=_ at firstRun
 rw [source_stack_push_1] at firstRun
 obtain ⟨capacityValue,secondOutput,capacityEval,secondRun,secondScope⟩:=funding_declaration_returned_context firstRun
 have loadedCapacity:=eval_fundingLoad first frame (232#64) index atCurrent (headerDomain 232 (by simp)) capacityAt
 have capacityEq : capacityValue=.val (.word index):=Option.some.inj (capacityEval.symm.trans loadedCapacity)
 subst capacityValue
 let second:=setVarHOLFinite (ofString "cap") (.val (.word index)) first
 change evaluateHOLFiniteState second (stackPushAt 2)=_ at secondRun
 have sp : second.locals.lookup (ofString "sp")=some (.val (.word index)) := by
  simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have cap : second.locals.lookup (ofString "cap")=some (.val (.word index)) := by
  simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have operand : second.locals.lookup (ofString "v")=some (fundingU256 a b c d) := by
  simpa (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atValue
 have result:=stack_push_growth_returned second secondOutput frame oldBase index scratch frontier a b c d watched value
  atCurrent sp cap operand (headerDomain 8 (by simp)) baseAt positive atScratch atFrontier ordered scratchBeforeFrame
  frameExtent scratchCap fullDomain above differentBase differentCounter differentCapacity code secondRun
 rw [firstScope,secondScope]
 exact result
#print axioms stack_push_growing_body_returned
end InitECandidate.Runtime
