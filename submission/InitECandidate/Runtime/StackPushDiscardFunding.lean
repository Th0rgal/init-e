import InitECandidate.Runtime.OriginalStackPushInstalled
import InitECandidate.Runtime.InterpreterFundingOperandStack
import InitECandidate.Runtime.InterpreterFundingMemoryTransport
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual installed stack_push call protects every live funding record and
its caller PC, with concrete operand buffer ownership/capacity. -/
theorem stack_push_discard_normal_funding {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (arguments : List (ExpHOL 64)) (base index capacity scratch frontier a b c d : BitVec 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d])
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (headerDomain : ∀offset∈([8,16,232] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+8)=.word base) (indexAt : s.memory (current.address+16)=.word index)
 (capacityAt : s.memory (current.address+232)=.word capacity)
 (positive : 1≤capacity.toNat) (capacityBound : capacity.toNat≤1024) (indexBound : index.toNat≤capacity.toNat)
 (bufferExtent : base.toNat+capacity.toNat*32≤current.address.toNat)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrontier : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)))
 (ordered : frontier≤scratch) (scratchBeforeFrame : scratch.toNat≤current.address.toNat)
 (frameExtent : current.address.toNat+280≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "stack_push") arguments)=(none,post)) :
 InterpreterFundingLayout post current.address.toNat upper (current::ancestors) ∧
 post.memory (current.address+0)=s.memory (current.address+0) ∧post.locals=s.locals ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 ∃nextScratch : BitVec 64,post.globals.lookup (ofString "scratch_ptr")=some (.val (.word nextScratch)) ∧nextScratch.toNat≤scratch.toNat ∧
 post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)) ∧post.globals.lookup (ofString "ev")=some (.val (.word current.address)) := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "v",fundingU256 a b c d)
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "stack_push") [fundingU256 a b c d]=some (sourceFunctionBody Guest.guestFn_stack_push,callee,.one) := by
  apply lookupCodeFinite_of_exact
  rw [code]
  simp [lookupCodeHOLExact,originalRuntimeCode_stackPush_lookup,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
  funext key
  by_cases same : key=ofString "v"
  · subst key;simp [callee,HolFiniteMapExact.lookup_update,FUPDATE,fundingU256]
  · simp [callee,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,same,Ne.symm same]
 obtain ⟨returned,body,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "stack_push") arguments _ _ callee .one args lookup run
 obtain ⟨other,otherBody,otherRun,globals,_⟩:=evaluate_discard_normal_body s post (ofString "stack_push") arguments _ _ callee .one args lookup run
 have equal : otherBody=body:=(Prod.mk.inj (bodyRun.symm.trans otherRun)).2.symm
 subst otherBody
 let entry:=callEntryStateHOLFinite s callee
 have atValue : entry.locals.lookup (ofString "v")=some (fundingU256 a b c d) := by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 rw [sourceFunctionBody_eq_structural] at bodyRun
 change evaluateHOLFiniteState entry (stackPushAt 0)=_ at bodyRun
 have entryLayout : InterpreterFundingLayout entry current.address.toNat upper (current::ancestors):=layout.after_memory rfl rfl
 obtain ⟨zero,paid,_⟩:=interpreter_funding_stack_push_returned entry body upper current ancestors entryLayout base index capacity scratch frontier a b c d returned atCurrent atValue headerDomain baseAt indexAt capacityAt positive capacityBound indexBound bufferExtent atScratch atFrontier ordered scratchBeforeFrame frameExtent fullDomain code bodyRun
 obtain ⟨_,pcKept,domain,endian,installed,nextScratch,scratchKept,scratchBound,frontierKept,evKept⟩:=stack_push_protected_returned entry body current.address base index capacity scratch frontier a b c d (current.address+0) returned atCurrent atValue headerDomain baseAt indexAt capacityAt positive capacityBound indexBound bufferExtent atScratch atFrontier ordered scratchBeforeFrame frameExtent fullDomain (by simp) (by intro equal;exact (by decide : (0#64)≠8#64) (add_left_cancel equal)) (by intro equal;exact (by decide : (0#64)≠16#64) (add_left_cancel equal)) (by intro equal;exact (by decide : (0#64)≠232#64) (add_left_cancel equal)) code bodyRun
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "stack_push") arguments)
 rw [run] at metadata
 refine ⟨paid.after_memory memory (metadata.2.1.trans domain.symm),?_,locals,metadata.2.1,metadata.2.2.1,metadata.1,nextScratch,?_,scratchBound,?_,?_⟩
 · rw [memory];exact pcKept
 · rw [globals];exact scratchKept
 · rw [globals];exact frontierKept
 · rw [globals];exact evKept
#print axioms stack_push_discard_normal_funding
end InitECandidate.Runtime
