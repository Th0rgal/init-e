import InitECandidate.Runtime.MptInsertPathsActive
import InitECandidate.Runtime.MptInsertStoppedStepWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The path-aware active invariant supplies every concrete premise of the
actual stopped iteration and yields its committed enlarged trie world. -/
theorem mpt_insert_paths_active_stopped {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier key length value valueLength : BitVec 64) (rank : Nat)
 (current : MptInsertPathsActive s live extensions branches size frontier key length value valueLength rank)
 (capacity : ∀node∈live,32≤size node) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 146≤s.clock)
 (stopped : post.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertLoopStep=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "result")=some (.val (.word root)) ∧(root=0 ∨root∈larger) ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧
 TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 obtain ⟨node,slot,level,root,atNode,atSlot,atLevel,atRoot,nodeValid,rootValid,typed,backlink,inside,rankEq⟩:=current.active.path
 exact mpt_insert_step_stopped_paths_world s post live extensions branches size frontier node key length level value valueLength
  slot root current.active.world current.kinds current.paths current.keyPath short nodeValid (capacity node) inside
  atNode current.active.atKey current.active.atLength atLevel current.active.atValue current.active.atValueLength
  current.active.domain code budget atSlot atRoot rootValid typed stopped run

#print axioms mpt_insert_paths_active_stopped
end InitECandidate.Runtime
