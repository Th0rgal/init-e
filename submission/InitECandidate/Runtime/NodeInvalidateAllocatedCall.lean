import InitECandidate.Runtime.NodeInvalidateAllocatedWorld
import InitECandidate.Runtime.OriginalNodeInvalidateCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
import InitECandidate.Runtime.PanDiscardNormalBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Same-run original node_invalidate discard-call closure. The full memory
domain and allocated record extent earn all three source store guards; no
minimum fuel or callee/frame premise is needed. -/
theorem node_invalidate_discard_normal_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier pointer : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (member : pointer∈live) (capacity : 32≤size pointer) (arguments : List (ExpHOL 64))
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word pointer)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "node_invalidate") arguments)=(none,post)) :
 AllocatedTrieWorld post live extensions branches size frontier ∧post.locals=s.locals ∧post.globals=s.globals ∧
 (∀watched : BitVec 64,watched≠pointer+8 →watched≠pointer+16 →watched≠pointer+24 →post.memory watched=s.memory watched) := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "nd",.val (.word pointer))
 have installed : s.code.lookup (ofString "node_invalidate")=some
  ([(ofString "nd",.one)],sourceFunctionBody Guest.guestFn_node_invalidate,.one) := by
  rw [code];exact originalRuntimeCode_nodeInvalidate_lookup
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "node_invalidate") (ofString "nd")
  (sourceFunctionBody Guest.guestFn_node_invalidate) pointer installed
 obtain ⟨value,bodyPost,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "node_invalidate") arguments _ _ callee .one args lookup run
 obtain ⟨other,otherPost,otherRun,globals,_⟩:=evaluate_discard_normal_body s post (ofString "node_invalidate") arguments _ _ callee .one args lookup run
 have same : otherPost=bodyPost:=(Prod.mk.inj (bodyRun.symm.trans otherRun)).2.symm
 subst otherPost
 have binding : (callEntryStateHOLFinite s callee).locals.lookup (ofString "nd")=some (.val (.word pointer)) := by
  simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have domain : ∀offset∈([8,16,24] : List Nat),s.memaddrs (pointer+BitVec.ofNat 64 offset) := by
  intro offset inside
  have small : offset<32 := by simp at inside;rcases inside with rfl|rfl|rfl <;> omega
  have before:=world.allocated pointer member
  apply fullDomain
  rw [world.layout.field_nat pointer member offset (by omega)]
  have:=world.capped;omega
 obtain ⟨actual,actualRun,actualWorld,_,actualGlobals,frame⟩:=evaluate_nodeInvalidate_allocated_world
  (callEntryStateHOLFinite s callee) live extensions branches size frontier pointer
  (world.after_memory_globals rfl rfl) member capacity binding domain
 have equal : bodyPost=actual:=(Prod.mk.inj (bodyRun.symm.trans actualRun)).2
 subst bodyPost
 have globalsKept : post.globals=s.globals:=globals.trans actualGlobals
 refine ⟨actualWorld.after_memory_globals memory globals,locals,globalsKept,?_⟩
 intro watched n8 n16 n24
 rw [memory]
 exact frame watched n8 n16 n24

#print axioms node_invalidate_discard_normal_world
end InitECandidate.Runtime
