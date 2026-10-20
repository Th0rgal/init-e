import InitECandidate.Runtime.StackPushNoGrowthPhysicalContext
import InitECandidate.Runtime.OriginalStackPushInstalled
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual installed non-growing push keeps the full physical context and old
record words, with the real caller scope restored. -/
theorem stack_push_no_growth_discard_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (arguments : List (ExpHOL 64)) (a b c d : BitVec 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d])
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "stack_push") arguments)=(none,post)) :
 EvmMemoryOperandAt post frame {words with stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.locals=s.locals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+16→post.memory watched=s.memory watched) := by
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
 have entryPhysical : EvmMemoryOperandAt entry frame words:=valid.after_context rfl rfl rfl
 have atValue : entry.locals.lookup (ofString "v")=some (fundingU256 a b c d) := by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 rw [sourceFunctionBody_eq_structural] at bodyRun
 change evaluateHOLFiniteState entry (stackPushAt 0)=_ at bodyRun
 obtain ⟨zero,physical,bodyGlobals,domain,endian,installed,upperFrame⟩:=stack_push_no_growth_returned_physical_context entry body frame words entryPhysical a b c d returned atValue inside fullDomain bodyRun
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "stack_push") arguments)
 rw [run] at metadata
 have postDomain : post.memaddrs=body.memaddrs:=metadata.2.1.trans domain.symm
 refine ⟨physical.after_context globals memory postDomain,globals.trans bodyGlobals,locals,metadata.2.1,metadata.2.2.1,metadata.1,?_⟩
 intro watched above different
 rw [memory]
 exact upperFrame watched above different
#print axioms stack_push_no_growth_discard_physical_context
end InitECandidate.Runtime
