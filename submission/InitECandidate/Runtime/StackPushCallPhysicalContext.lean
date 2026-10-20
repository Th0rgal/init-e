import InitECandidate.Runtime.StackPushBoolPhysicalContext
import InitECandidate.Runtime.StackPushWordPhysicalContext
import InitECandidate.Runtime.OriginalStackPushBoolInstalled
import InitECandidate.Runtime.OriginalStackPushWordInstalled
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
private theorem bool_callee_lookup {F : Type} (s : PanSemStateFiniteExact 64 F) (b : BitVec 64)
 (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (ofString "stack_push_bool") [.val (.word b)]=
 some (stackPushBoolBody,HolFiniteMapExact.empty.update (ofString "b",.val (.word b)),.one) := by
 apply lookupCodeFinite_of_exact
 rw [code]
 simp [lookupCodeHOLExact,originalRuntimeCode_stackPushBool_lookup,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
 refine ⟨rfl,?_⟩
 funext key
 by_cases same : key=ofString "b"
 · subst key;simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty]
 · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,same,Ne.symm same]
private theorem word_callee_lookup {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
 (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (ofString "stack_push_word") [.val (.word w)]=
 some (stackPushWordBody,HolFiniteMapExact.empty.update (ofString "w",.val (.word w)),.one) := by
 apply lookupCodeFinite_of_exact
 rw [code]
 simp [lookupCodeHOLExact,originalRuntimeCode_stackPushWord_lookup,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
 refine ⟨rfl,?_⟩
 funext key
 by_cases same : key=ofString "w"
 · subst key;simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty]
 · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,same,Ne.symm same]
/-- Real installed `stack_push_bool` declaration call: pushes the boolean
word chosen by the checked argument and restores the caller locals. -/
theorem stack_push_bool_discard_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (argument : ExpHOL 64) (b : BitVec 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) [argument]=some [.val (.word b)])
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "stack_push_bool") [argument])=(none,post)) :
 EvmMemoryOperandAt post frame {words with stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.locals=s.locals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+16→post.memory watched=s.memory watched) := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "b",.val (.word b))
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "stack_push_bool") [.val (.word b)]=some (stackPushBoolBody,callee,.one) := bool_callee_lookup s b code
 obtain ⟨returned,body,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "stack_push_bool") [argument] [.val (.word b)] stackPushBoolBody callee .one args lookup run
 obtain ⟨other,otherBody,otherRun,globals,_⟩:=evaluate_discard_normal_body s post (ofString "stack_push_bool") [argument] [.val (.word b)] stackPushBoolBody callee .one args lookup run
 have equal : otherBody=body:=(Prod.mk.inj (bodyRun.symm.trans otherRun)).2.symm
 subst otherBody
 let entry:=callEntryStateHOLFinite s callee
 have entryPhysical : EvmMemoryOperandAt entry frame words:=valid.after_context rfl rfl rfl
 have atB : entry.locals.lookup (ofString "b")=some (.val (.word b)) := by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨zero,physical,bodyGlobals,domain,endian,installed,upperFrame⟩:=stack_push_bool_returned_physical_context entry body frame words entryPhysical b returned atB inside fullDomain code bodyRun
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "stack_push_bool") [argument])
 rw [run] at metadata
 have postDomain : post.memaddrs=body.memaddrs:=metadata.2.1.trans domain.symm
 refine ⟨physical.after_context globals memory postDomain,globals.trans bodyGlobals,locals,metadata.2.1,metadata.2.2.1,metadata.1,?_⟩
 intro watched above different
 rw [memory]
 exact upperFrame watched above different
/-- Real installed `stack_push_word` declaration call: pushes the checked
word as a four-limb struct and restores the caller locals. -/
theorem stack_push_word_discard_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (argument : ExpHOL 64) (w : BitVec 64)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) [argument]=some [.val (.word w)])
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "stack_push_word") [argument])=(none,post)) :
 EvmMemoryOperandAt post frame {words with stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.locals=s.locals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+16→post.memory watched=s.memory watched) := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "w",.val (.word w))
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "stack_push_word") [.val (.word w)]=some (stackPushWordBody,callee,.one) := word_callee_lookup s w code
 obtain ⟨returned,body,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "stack_push_word") [argument] [.val (.word w)] stackPushWordBody callee .one args lookup run
 obtain ⟨other,otherBody,otherRun,globals,_⟩:=evaluate_discard_normal_body s post (ofString "stack_push_word") [argument] [.val (.word w)] stackPushWordBody callee .one args lookup run
 have equal : otherBody=body:=(Prod.mk.inj (bodyRun.symm.trans otherRun)).2.symm
 subst otherBody
 let entry:=callEntryStateHOLFinite s callee
 have entryPhysical : EvmMemoryOperandAt entry frame words:=valid.after_context rfl rfl rfl
 have atW : entry.locals.lookup (ofString "w")=some (.val (.word w)) := by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨zero,physical,bodyGlobals,domain,endian,installed,upperFrame⟩:=stack_push_word_returned_physical_context entry body frame words entryPhysical w returned atW inside fullDomain code bodyRun
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "stack_push_word") [argument])
 rw [run] at metadata
 have postDomain : post.memaddrs=body.memaddrs:=metadata.2.1.trans domain.symm
 refine ⟨physical.after_context globals memory postDomain,globals.trans bodyGlobals,locals,metadata.2.1,metadata.2.2.1,metadata.1,?_⟩
 intro watched above different
 rw [memory]
 exact upperFrame watched above different
#print axioms stack_push_bool_discard_physical_context
#print axioms stack_push_word_discard_physical_context
end InitECandidate.Runtime
