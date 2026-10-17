import InitECandidate.Runtime.TrieWalkBranchChildAddress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Registered branch slots contain null or live children. -/
def BranchChildrenIn {F : Type} (live branches : Set (BitVec 64)) (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ node ∈ branches, ∀ slot : Nat, slot < 16 → ∀ child : BitVec 64,
    state.memory (branchChildAddress node slot) = .word child → child = 0 ∨ child ∈ live

/-- Every readable byte within the logical nibble buffer is a nibble. Failed
reads remain allowed and are handled by the source error paths. -/
def TrieNibbleRange {F : Type} (state : PanSemStateFiniteExact 64 F) (nibs length : BitVec 64) : Prop :=
  ∀ offset : Nat, offset < length.toNat → ∀ byte : UInt8,
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (nibs + BitVec.ofNat 64 offset) = some byte → byte.toNat < 16

theorem branchChildrenIn_empty {F : Type} (live : Set (BitVec 64)) (state : PanSemStateFiniteExact 64 F) :
    BranchChildrenIn live ∅ state := by intro node member; cases member

theorem BranchChildrenIn.mono {F : Type} {state : PanSemStateFiniteExact 64 F}
    {live larger branches : Set (BitVec 64)} (included : live ⊆ larger)
    (valid : BranchChildrenIn live branches state) : BranchChildrenIn larger branches state := by
  intro node member slot inside child loaded
  rcases valid node member slot inside child loaded with zero | old
  · exact Or.inl zero
  · exact Or.inr (included old)

theorem BranchChildrenIn.after_memory {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {live branches : Set (BitVec 64)} (valid : BranchChildrenIn live branches state)
    (memory : post.memory = state.memory) : BranchChildrenIn live branches post := by
  intro node member slot inside child loaded
  rw [memory] at loaded
  exact valid node member slot inside child loaded

theorem TrieNibbleRange.after_frame {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {nibs length : BitVec 64} (valid : TrieNibbleRange state nibs length)
    (memory : post.memory = state.memory) (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    TrieNibbleRange post nibs length := by
  intro offset inside byte loaded
  apply valid offset inside byte
  have readEqual : @panMemLoadByteHOL 64 _ post.memory post.memaddrs
      (fun address => Classical.propDecidable (post.memaddrs address)) post.be (nibs + BitVec.ofNat 64 offset) =
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (nibs + BitVec.ofNat 64 offset) := by
    have sameDomain := Iff.of_eq (congrFun domain (panByteAlignHOL (nibs + BitVec.ofNat 64 offset)))
    by_cases accessible : state.memaddrs (panByteAlignHOL (nibs + BitVec.ofNat 64 offset))
    · have postAccessible := sameDomain.mpr accessible
      simp [panMemLoadByteHOL,memory,endian,accessible,postAccessible]
    · have postInaccessible : ¬post.memaddrs (panByteAlignHOL (nibs + BitVec.ofNat 64 offset)) := fun present => accessible (sameDomain.mp present)
      simp [panMemLoadByteHOL,accessible,postInaccessible]
  exact readEqual.symm.trans loaded

#print axioms branchChildrenIn_empty
#print axioms BranchChildrenIn.mono
#print axioms BranchChildrenIn.after_memory
#print axioms TrieNibbleRange.after_frame
end InitECandidate.Runtime
