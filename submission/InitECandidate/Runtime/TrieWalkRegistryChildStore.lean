import InitECandidate.Runtime.TrieWalkRegistry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A child-pointer write retains live edges. Kind and extension-length cells
must be separate; replacing an empty extension edge also requires a smaller
child, precisely the ordering used by the traversal rank. -/
theorem TrieWalkRegistry.write_child {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (address child : BitVec 64)
    (registry : TrieWalkRegistry live extensions branches state)
    (childValid : child = 0 ∨ child ∈ live)
    (kindsSeparate : ∀ node ∈ live, node ≠ address)
    (lengthsSeparate : ∀ node ∈ extensions, node + BitVec.ofNat 64 40 ≠ address)
    (ordered : ∀ node ∈ extensions, node + BitVec.ofNat 64 48 = address →
      state.memory (node + BitVec.ofNat 64 40) = .word 0 → child.toNat < node.toNat) :
    TrieWalkRegistry live extensions branches (sourceWriteWord state address child) := by
  constructor
  · intro node member next empty loaded
    have oldEmpty : state.memory (node + BitVec.ofNat 64 40) = .word 0 := by
      simpa [sourceWriteWord,lengthsSeparate node member] using empty
    by_cases same : node + BitVec.ofNat 64 48 = address
    · have nextEq : child = next := by simpa [sourceWriteWord,same] using loaded
      rw [← nextEq]
      exact ordered node member same oldEmpty
    · have oldLoaded : state.memory (node + BitVec.ofNat 64 48) = .word next := by
        simpa [sourceWriteWord,same] using loaded
      exact registry.order node member next oldEmpty oldLoaded
  · intro node member next loaded
    by_cases same : node + BitVec.ofNat 64 48 = address
    · have nextEq : child = next := by simpa [sourceWriteWord,same] using loaded
      rw [← nextEq]
      exact childValid
    · apply registry.extensionChildren node member next
      simpa [sourceWriteWord,same] using loaded
  · intro node member slot small next loaded
    by_cases same : branchChildAddress node slot = address
    · have nextEq : child = next := by simpa [sourceWriteWord,same] using loaded
      rw [← nextEq]
      exact childValid
    · apply registry.branchChildren node member slot small next
      simpa [sourceWriteWord,same] using loaded
  · intro node member loaded
    apply registry.extensionKind node member
    simpa [sourceWriteWord,kindsSeparate node member] using loaded
  · intro node member kind loaded nonzero nonleaf nonext
    apply registry.branchKind node member kind _ nonzero nonleaf nonext
    simpa [sourceWriteWord,kindsSeparate node member] using loaded

/-- The registry update is realized by the original source store evaluator,
with explicit expression evaluation and memory-access guards. -/
theorem evaluate_registry_child_store {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (address child : BitVec 64)
    (destination expression : ExpHOL 64)
    (registry : TrieWalkRegistry live extensions branches state)
    (childValid : child = 0 ∨ child ∈ live)
    (kindsSeparate : ∀ node ∈ live, node ≠ address)
    (lengthsSeparate : ∀ node ∈ extensions, node + BitVec.ofNat 64 40 ≠ address)
    (ordered : ∀ node ∈ extensions, node + BitVec.ofNat 64 48 = address →
      state.memory (node + BitVec.ofNat 64 40) = .word 0 → child.toNat < node.toNat)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) destination = some (.val (.word address)))
    (childEval : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression = some (.val (.word child)))
    (domain : state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state (.store destination expression) = (none,post) ∧
      TrieWalkRegistry live extensions branches post ∧ post.clock = state.clock ∧ post.locals = state.locals := by
  exact ⟨_,evaluate_store_word state address child destination expression addressEval childEval domain,
    registry.write_child state live extensions branches address child childValid kindsSeparate lengthsSeparate ordered,rfl,rfl⟩

#print axioms TrieWalkRegistry.write_child
#print axioms evaluate_registry_child_store
end InitECandidate.Runtime
