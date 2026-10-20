import InitECandidate.Runtime.PtKeyUCopyCallGD
import InitECandidate.Runtime.MemcpyAlignedCombinedCall
import InitECandidate.Runtime.HashOccupancyPreservation
/-!
The unaligned counterpart of root's `evaluate_memcpy_aligned_call_with_frame`: same conclusion (normal completion,
occupancy count of a separate byte array kept, every word outside the destination's words and cells kept), for
operands that are not both 8-aligned (`sourceAligned` replaced by the source condition and `8 ≤ n`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_memcpy_unaligned_call_with_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destinationArgument sourceArgument sizeArgument : ExpHOL 64)
    (destination source size capacity used : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (unal : (destination ||| source) &&& 7 ≠ 0) (size8 : 8 ≤ size.toNat) (budget : size.toNat + 1 ≤ state.clock)
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (sourceByteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (code : state.code = originalRuntimeCode)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [destinationArgument,sourceArgument,sizeArgument] =
        some [.val (.word destination),.val (.word source),.val (.word size)]) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy")
        [destinationArgument,sourceArgument,sizeArgument]) = (none,post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used) ∧
      state.clock ≤ post.clock + size.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals ∧
      ∀ watched : BitVec 64,
        (∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset) →
        (∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) →
        post.memory watched = state.memory watched := by
  have notW : ∀ w : BitVec 64, (∀ offset : Nat, offset < size.toNat → w ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) →
      ¬ cpW destination size w := by
    rintro w h ⟨k, hk, rfl⟩
    exact h k.toNat hk (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
  obtain ⟨post, run, c1, c2, hG, hC, hD, hB, hL, hM⟩ := evaluate_memcpy_unaligned_call state destinationArgument sourceArgument
    sizeArgument destination source size code arguments unal (by omega)
    (fun x hx => by
      have := x.isLt
      have e : BitVec.ofNat 64 x.toNat = x := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact ⟨e ▸ byteDomain x.toNat hx, e ▸ sourceByteDomain x.toNat hx⟩)
    (by omega)
  refine ⟨post, run, ?_, by omega, c2, hG, hC, hD, hB, hL, fun w _ bytes => hM w (notW w bytes)⟩
  apply hashOccupiedCount_congr
  intro index inside
  have hm := hM _ (notW _ (fun off h => byteSeparate off h index inside))
  unfold hashOccupancyRead panMemLoadByteHOL
  simp only [hm]
  cases hcell : state.memory (panByteAlignHOL (used + index)) with
  | word v =>
    dsimp only
    by_cases hd : state.memaddrs (panByteAlignHOL (used + index))
    · have hd' : post.memaddrs (panByteAlignHOL (used + index)) := by rw [hD]; exact hd
      rw [if_pos hd, if_pos hd', hB]
      try simp [hcell]
    · have hd' : ¬ post.memaddrs (panByteAlignHOL (used + index)) := by rw [hD]; exact hd
      rw [if_neg hd, if_neg hd']

#print axioms evaluate_memcpy_unaligned_call_with_frame
end InitECandidate.Runtime
