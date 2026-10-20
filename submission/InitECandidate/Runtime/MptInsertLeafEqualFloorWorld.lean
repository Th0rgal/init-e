import InitECandidate.Runtime.MptInsertLeafMatchedAllocationFloor
import InitECandidate.Runtime.MptInsertLeafMatchedTransport
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returning from the actual equality guard necessarily executes the real
leaf payload stores and returns the original node, keeping all stored and
incoming path buffers. No assumed comparison answer is needed. -/
theorem mpt_insert_leaf_equal_returned_floor_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier node value length : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (member : node∈live) (tag : s.memory node=.word (1#64))
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atLength : s.locals.lookup (ofString "vlen")=some (.val (.word length)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s mptInsertLeafEqualReturn=(some (.returned returned),post)) :
 returned=.val (.word node) ∧
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNodeKinds post live extensions branches ∧
 TrieNodePaths post live extensions branches size frontier ∧post.globals=s.globals ∧
 TrieAllocationFloor post live branches floor ∧
 (∀key len,TriePathBuffer s live size key len frontier→TriePathBuffer post live size key len frontier) := by
 rw [source_mpt_insert_leaf_equal_return,evaluateHOLFiniteState_ite] at run
 split at run
 · split at run
   · rw [evaluateHOLFiniteState_skip] at run
     cases run
   · obtain ⟨matched,matchedRun,worldOut,kindsOut,pathsOut,globals,transport⟩:=
      evaluate_mpt_insert_leaf_matched_transport_world s live extensions branches size frontier node value length
       world kinds paths member tag atNode atValue atLength fullDomain
     have same:=Prod.mk.inj (matchedRun.symm.trans run)
     have valueEq : returned=.val (.word node):=by simpa using same.1.symm
     have postEq : matched=post:=same.2
     subst matched
     obtain ⟨other,otherRun,lowerOut⟩:=evaluate_mpt_insert_leaf_matched_allocation_floor
      s live extensions branches size frontier node value length world kinds paths floor lower
      member tag atNode atValue atLength fullDomain
     have samePost : other=post:=(Prod.mk.inj (otherRun.symm.trans matchedRun)).2
     subst other
     exact ⟨valueEq,worldOut,kindsOut,pathsOut,globals,lowerOut,transport⟩
 · simp at run

#print axioms mpt_insert_leaf_equal_returned_floor_world
end InitECandidate.Runtime
