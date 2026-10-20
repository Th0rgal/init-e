import InitECandidate.Runtime.TrieAllocationFloorStore
import InitECandidate.Runtime.NodeInvalidatePathsWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Actual cache invalidation preserves the earlier trie-header allocation floor. -/
theorem node_invalidate_discard_normal_allocation_floor {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier pointer : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (member : pointer∈live) (capacity : 32≤size pointer) (arguments : List (ExpHOL 64))
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word pointer)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "node_invalidate") arguments)=(none,post)) :
 TrieAllocationFloor post live branches floor := by
 obtain ⟨worldOut,kindsOut,locals,globals,frame⟩:=node_invalidate_discard_normal_kinds_world s post live extensions branches size frontier pointer world kinds member capacity arguments args fullDomain code run
 apply lower.after_record_fields paths world pointer member [8,16,24]
 · intro field included
   simp only [List.mem_cons,List.not_mem_nil,or_false] at included
   rcases included with rfl|rfl|rfl <;>omega
 · right;intro field included
   simp only [List.mem_cons,List.not_mem_nil,or_false] at included
   rcases included with rfl|rfl|rfl <;>decide
 · intro watched separate
   exact frame watched (separate 8 (by simp)) (separate 16 (by simp)) (separate 24 (by simp))

#print axioms node_invalidate_discard_normal_allocation_floor
end InitECandidate.Runtime
