import InitECandidate.Runtime.NodeInvalidateAllocatedCall
import InitECandidate.Runtime.TrieNodeKinds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual cache-invalidating call preserves exact node kinds as well as
the allocated traversal world. Each kind address is disjoint from the three
real metadata stores by allocated record geometry. -/
theorem node_invalidate_discard_normal_kinds_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier pointer : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (member : pointer∈live) (capacity : 32≤size pointer) (arguments : List (ExpHOL 64))
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word pointer)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "node_invalidate") arguments)=(none,post)) :
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNodeKinds post live extensions branches ∧
 post.locals=s.locals ∧post.globals=s.globals ∧
 (∀watched : BitVec 64,watched≠pointer+8 →watched≠pointer+16 →watched≠pointer+24 →post.memory watched=s.memory watched) := by
 obtain ⟨worldOut,locals,globals,frame⟩:=node_invalidate_discard_normal_world s post live extensions branches size frontier pointer world member capacity arguments args fullDomain code run
 refine ⟨worldOut,?_,locals,globals,frame⟩
 apply kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive
 intro node registered
 have separate (offset : Nat) (positive : 0<offset) (small : offset<32) : node≠pointer+BitVec.ofNat 64 offset := by
  simpa using world.layout.fields_ne node pointer registered member 0 offset
   (world.layout.positive node registered) (by omega) (Or.inr (by omega))
 exact frame node (separate 8 (by decide) (by decide)) (separate 16 (by decide) (by decide)) (separate 24 (by decide) (by decide))

#print axioms node_invalidate_discard_normal_kinds_world
end InitECandidate.Runtime
