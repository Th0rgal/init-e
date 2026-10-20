import InitECandidate.Runtime.TrieNodePaths
import InitECandidate.Runtime.TriePathBufferFieldsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
/-- Shared header framing for path contents and allocation-floor invariants. -/
theorem TrieNodePaths.stored_header_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier : BitVec 64}
 (paths : TrieNodePaths s live extensions branches size frontier)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (parent : BitVec 64) (member : parent∈live) (fields : List Nat)
 (inside : ∀field∈fields,field<size parent)
 (headerSafe : parent∈branches ∨∀field∈fields,field≠32 ∧field≠40)
 (frame : ∀watched : BitVec 64,(∀field∈fields,watched≠parent+BitVec.ofNat 64 field)→post.memory watched=s.memory watched)
 (node : BitVec 64) (registered : node∈live) (nonBranch : node∉branches)
 (header : Nat) (which : header=32 ∨header=40) :
 post.memory (node+BitVec.ofNat 64 header)=s.memory (node+BitVec.ofNat 64 header) := by
 apply frame
 intro field included
 have capacity:=paths.header_capacity world.layout node registered nonBranch
 apply world.layout.fields_ne node parent registered member header field
  (by rcases which with rfl|rfl <;>omega) (inside field included)
 by_cases same : node=parent
 · subst node;right
   rcases headerSafe with branch|safe
   · exact False.elim (nonBranch branch)
   · rcases which with rfl|rfl
     · exact Ne.symm (safe field included).1
     · exact Ne.symm (safe field included).2
 · exact Or.inl same

#print axioms TrieNodePaths.stored_header_frame
end InitECandidate.Runtime
