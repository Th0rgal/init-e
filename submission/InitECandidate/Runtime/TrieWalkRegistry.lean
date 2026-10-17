import InitECandidate.Runtime.TrieWalkStepLiveProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Memory-based facts needed to follow any live trie node. Terminal node
kinds need no child registry; only extensions require address ordering. -/
structure TrieWalkRegistry {F : Type} (live extensions branches : Set (BitVec 64))
    (state : PanSemStateFiniteExact 64 F) : Prop where
  order : ExtensionOrderFamily extensions state
  extensionChildren : ExtensionChildrenIn live extensions state
  branchChildren : BranchChildrenIn live branches state
  extensionKind : ∀ node ∈ live, state.memory node = .word 2 → node ∈ extensions
  branchKind : ∀ node ∈ live, ∀ kind : BitVec 64, state.memory node = .word kind →
    kind ≠ 0 → kind ≠ 1 → kind ≠ 2 → node ∈ branches

theorem TrieWalkRegistry.after_memory {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {live extensions branches : Set (BitVec 64)}
    (valid : TrieWalkRegistry live extensions branches state) (memory : post.memory = state.memory) :
    TrieWalkRegistry live extensions branches post := by
  constructor
  · intro node member child empty loaded
    rw [memory] at empty loaded
    exact valid.order node member child empty loaded
  · intro node member child loaded
    rw [memory] at loaded
    exact valid.extensionChildren node member child loaded
  · exact valid.branchChildren.after_memory memory
  · intro node member loaded
    rw [memory] at loaded
    exact valid.extensionKind node member loaded
  · intro node member kind loaded nonzero nonleaf nonext
    rw [memory] at loaded
    exact valid.branchKind node member kind loaded nonzero nonleaf nonext

#print axioms TrieWalkRegistry.after_memory
end InitECandidate.Runtime
