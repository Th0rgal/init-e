import InitECandidate.Runtime.TrieNodePaths
import InitECandidate.Runtime.TriePathBufferFieldsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A finite set of real record-field changes preserves all stored paths.
Concrete callers discharge the frame with their actual source stores; the
header and byte-cell exclusions follow from allocated record geometry. -/
theorem TrieNodePaths.after_record_fields {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (paths : TrieNodePaths s live extensions branches size frontier)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (parent : BitVec 64) (member : parent∈live) (fields : List Nat)
 (inside : ∀field∈fields,field<size parent)
 (headerSafe : parent∈branches ∨∀field∈fields,field≠32 ∧field≠40)
 (frame : ∀watched : BitVec 64,(∀field∈fields,watched≠parent+BitVec.ofNat 64 field)→post.memory watched=s.memory watched)
 (domain : post.memaddrs=s.memaddrs) (endian : post.be=s.be) :
 TrieNodePaths post live extensions branches size frontier := by
 refine ⟨paths.leafCapacity,?_⟩
 intro node registered nonBranch
 obtain ⟨key,len,keyAt,lenAt,short,path⟩:=paths.paths node registered nonBranch
 have headerFrame (header : Nat) (which : header=32 ∨header=40) :
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
 have keptPath:=path.after_record_fields world parent member fields inside frame domain endian
 refine ⟨key,len,?_,?_,short,keptPath⟩
 · rw [show node+32=node+BitVec.ofNat 64 32 from rfl,headerFrame 32 (Or.inl rfl)];exact keyAt
 · rw [show node+40=node+BitVec.ofNat 64 40 from rfl,headerFrame 40 (Or.inr rfl)];exact lenAt

#print axioms TrieNodePaths.after_record_fields
end InitECandidate.Runtime
