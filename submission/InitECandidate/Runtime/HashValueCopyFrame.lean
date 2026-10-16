import InitECandidate.Runtime.HashValueFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A copy's cell frame transfers bounded reverse positions when it protects
both aligned occupancy cells and reverse-array cells. -/
theorem HashValueEntriesWord.copy_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (used values capacity destination size : BitVec 64)
    (entries : HashValueEntriesWord used values capacity state)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (frame : ∀ cell : BitVec 64,
      (∀ offset : Nat, offset < size.toNat → cell ≠ destination + BitVec.ofNat 64 offset) →
      (∀ offset : Nat, offset < size.toNat → cell ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) →
      post.memory cell = state.memory cell)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < size.toNat →
      panByteAlignHOL (used + slot) ≠ destination + BitVec.ofNat 64 offset ∧
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (valueSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < size.toNat →
      values + slot * 8 ≠ destination + BitVec.ofNat 64 offset ∧
      values + slot * 8 ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) :
    HashValueEntriesWord used values capacity post := by
  apply entries.framed state post used values capacity
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
    exact frame _ (fun offset bound => (valueSeparate slot inside offset bound).1)
      (fun offset bound => (valueSeparate slot inside offset bound).2)

#print axioms HashValueEntriesWord.copy_frame
end InitECandidate.Runtime
