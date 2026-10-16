import InitECandidate.Runtime.HashReverseEntriesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A copy's cell frame transfers bounded reverse positions when it protects
both aligned occupancy cells and reverse-array cells. -/
theorem HashReverseEntriesBound.copy_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (used orderPos capacity items destination size : BitVec 64)
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (frame : ∀ cell : BitVec 64,
      (∀ offset : Nat, offset < size.toNat → cell ≠ destination + BitVec.ofNat 64 offset) →
      (∀ offset : Nat, offset < size.toNat → cell ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) →
      post.memory cell = state.memory cell)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < size.toNat →
      panByteAlignHOL (used + slot) ≠ destination + BitVec.ofNat 64 offset ∧
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < size.toNat →
      orderPos + slot * 8 ≠ destination + BitVec.ofNat 64 offset ∧
      orderPos + slot * 8 ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) :
    HashReverseEntriesBound used orderPos capacity items post := by
  apply entries.framed state post used orderPos capacity items
  · intro slot inside
    have cell := frame (panByteAlignHOL (used + slot))
      (fun offset bound => (occupancySeparate slot inside offset bound).1)
      (fun offset bound => (occupancySeparate slot inside offset bound).2)
    cases state
    cases post
    dsimp only at *
    subst_vars
    simp [hashOccupancyRead,panMemLoadByteHOL,cell]
  · intro slot inside
    exact frame _ (fun offset bound => (reverseSeparate slot inside offset bound).1)
      (fun offset bound => (reverseSeparate slot inside offset bound).2)

#print axioms HashReverseEntriesBound.copy_frame
end InitECandidate.Runtime
