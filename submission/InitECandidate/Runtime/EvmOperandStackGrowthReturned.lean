import InitECandidate.Runtime.EvmOperandStackGrowthResized
import InitECandidate.Runtime.EvmOperandStackGrowthGuard
import InitECandidate.Runtime.EvmOperandStackWriteHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The original stack_push growth choice through its actual return. Fresh
capacity/extent are derived from the real guard, clamp and scratch allocator;
all four data writes are below the old scratch frontier. -/
theorem stack_push_growth_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame oldBase index scratch frontier a b c d watched : BitVec 64) (value : ValueHOL 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atIndex : s.locals.lookup (ofString "sp")=some (.val (.word index)))
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word index)))
 (atValue : s.locals.lookup (ofString "v")=some (fundingU256 a b c d))
 (baseDomain : s.memaddrs (frame+8)) (baseAt : s.memory (frame+8)=.word oldBase)
 (positive : 1≤index.toNat)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrontier : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)))
 (ordered : frontier≤scratch) (scratchBeforeFrame : scratch.toNat≤frame.toNat)
 (frameExtent : frame.toNat+280≤33806089496) (scratchCap : scratch.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (above : scratch.toNat≤watched.toNat) (differentBase : watched≠frame+8)
 (differentCounter : watched≠frame+16) (differentCapacity : watched≠frame+232)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (stackPushAt 2)=(some (.returned value),post)) :
 let grown:=stackPushGrownCapacity index
 let fresh:=scratchAllocationEnd scratch (grown*32#64)
 value=.val (.word 0) ∧post.memory watched=s.memory watched ∧
 post.memory (frame+16)=.word (index+1) ∧
 post.memory (frame+8)=.word fresh ∧post.memory (frame+232)=.word grown ∧
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word fresh)) ∧
 frontier.toNat≤fresh.toNat ∧fresh.toNat+grown.toNat*32≤scratch.toNat ∧
 index.toNat+1≤grown.toNat ∧grown.toNat≤1024 ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have metadata:=evaluateHOLFiniteState_metadata s (stackPushAt 2)
 rw [run] at metadata
 rw [source_stack_push_2] at run
 obtain ⟨afterGrowth,growthRun,nextRun⟩:=seq_returned_of_nonreturning_first
  (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) s v) run
 have growthCondition : @evalHOLExact 64 F _ s.toExact (fun address=>Classical.propDecidable (s.memaddrs address))
  (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap")))=some (.val (.word 1)) := by
  simp [evalHOLExact,atIndex,atCapacity,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
 rw [evaluateHOLFiniteState_ite,growthCondition] at growthRun
 change evaluateHOLFiniteState s (stackPushGrowthAt 0)=(none,afterGrowth) at growthRun
 obtain ⟨small,resizedRun⟩:=stack_push_growth_guard_normal s afterGrowth index atCapacity growthRun
 obtain ⟨newBase,newCapacity,kept,globals,lower,extent,inside,capacityBound,domain,endian,installed,locals⟩:=
  stack_push_growth_resized_normal s afterGrowth frame oldBase index index scratch frontier watched
  atCurrent atIndex atCapacity baseDomain baseAt (by omega) positive small atScratch atFrontier ordered scratchCap
  above differentBase differentCapacity code resizedRun
 have sp : afterGrowth.locals.lookup (ofString "sp")=some (.val (.word index)) := by
  rw [locals _ (by decide) (by decide)];exact atIndex
 have operand : afterGrowth.locals.lookup (ofString "v")=some (fundingU256 a b c d) := by
  rw [locals _ (by decide) (by decide)];exact atValue
 have current : afterGrowth.globals.lookup (ofString "ev")=some (.val (.word frame)) := by
  rw [globals]
  simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atCurrent
 rw [source_stack_push_3] at nextRun
 obtain ⟨afterLimit,limitRun,writeRun⟩:=seq_returned_of_nonreturning_first
  (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) afterGrowth v) nextRun
 have notLimit : index≠1024#64 := by intro equal;have h:=congrArg BitVec.toNat equal;change index.toNat=1024 at h;omega
 have limitCondition : @evalHOLExact 64 F _ afterGrowth.toExact (fun address=>Classical.propDecidable (afterGrowth.memaddrs address))
  (.cmp .equal (.var .local (ofString "sp")) (.const 1024))=some (.val (.word 0)) := by
  simp [evalHOLExact,sp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,notLimit]
 rw [evaluateHOLFiniteState_ite,limitCondition] at limitRun
 change evaluateHOLFiniteState afterGrowth .skip=(none,afterLimit) at limitRun
 rw [evaluateHOLFiniteState_skip] at limitRun
 have same : afterLimit=afterGrowth := (Prod.mk.inj limitRun).2.symm
 subst afterLimit
 have destinations:=stack_push_fresh_destinations_domain afterGrowth
  (scratchAllocationEnd scratch (stackPushGrownCapacity index*32#64)) index (stackPushGrownCapacity index) scratch
  inside capacityBound extent scratchCap (by intro address bounded;rw [domain];exact fullDomain address bounded)
 obtain ⟨returned,postEq⟩:=stack_push_write_suffix_returned afterGrowth post frame
  (scratchAllocationEnd scratch (stackPushGrownCapacity index*32#64)) index a b c d value current sp operand
  (by rw [domain];exact baseDomain) newBase destinations writeRun
 have header:=stack_push_write_header afterGrowth frame (scratchAllocationEnd scratch (stackPushGrownCapacity index*32#64)) index (stackPushGrownCapacity index) a b c d inside capacityBound (by omega) frameExtent
 refine ⟨returned,?_,?_,?_,?_,?_,lower,extent,inside,capacityBound,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [postEq]
   exact (stack_push_write_suffix_frame afterGrowth frame _ index a b c d watched differentCounter
    (stack_push_fresh_destinations_separate _ index (stackPushGrownCapacity index) scratch watched inside capacityBound extent scratchCap above)).trans kept
 · rw [postEq]
   change (if frame+16#64=frame+16#64 then HolWordLab.word (index+1#64) else _) = _
   rw [if_pos rfl]
   congr 1 <;> bv_decide
 · rw [postEq];exact header.1.trans newBase
 · rw [postEq];exact header.2.1.trans newCapacity
 · rw [postEq];exact globals
#print axioms stack_push_growth_returned
end InitECandidate.Runtime
