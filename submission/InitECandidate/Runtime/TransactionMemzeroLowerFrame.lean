import InitECandidate.Runtime.MemzeroAlignedCombinedCall
import InitECandidate.Runtime.MemzeroIntervalDomains
import InitECandidate.Runtime.RlpSliceInputPrefix
import InitECandidate.Runtime.RlpSliceAddressSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Clearing the fresh transaction record preserves every older memory word,
including byte stores whose destinations are aligned down to word cells. -/
theorem evaluate_transaction_memzero_lower_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (code : state.code = originalRuntimeCode) (budget : 401 ≤ state.clock)
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (arena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memzero")
        [.var .local (ofString "tx"),.const 400]) = (none,post) ∧
      post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧
      ∀ watched : BitVec 64, watched.toNat < tx.toNat → post.memory watched = state.memory watched := by
  have fits : tx.toNat + (400 : BitVec 64).toNat ≤ 2^64 := by change tx.toNat + 400 ≤ 2^64; omega
  obtain ⟨words,bytes⟩ := memzero_interval_domains state tx 400 aligned fits arena
  obtain ⟨post,run,_,_,_,globals,_,domain,_,_,_,frame⟩ := evaluate_memzero_aligned_call_with_frame state
    (.var .local (ofString "tx")) (.const 400) tx 400
    (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,txLocal]) code budget small aligned words bytes
  refine ⟨post,run,globals,domain,?_⟩
  intro watched before
  apply frame watched
  · intro offset inside same
    have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by change offset < 400 at inside; omega)
    have address : (tx + BitVec.ofNat 64 offset).toNat = tx.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; change offset < 400 at inside; omega),offsetNat]
    have equal := congrArg BitVec.toNat same
    rw [address] at equal
    omega
  · intro offset inside same
    have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by change offset < 400 at inside; omega)
    have lower := (hashOccupancy_aligned_interval tx 400 (BitVec.ofNat 64 offset) aligned fits
      (by rw [offsetNat]; exact inside)).1
    rw [← same] at lower
    omega

/-- Older readable slice entries survive any memory change confined above
an allocation boundary. Their pure byte-span bounds are retained verbatim. -/
theorem rlp_slice_input_prefix_after_lower_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count input inputLength boundary : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ boundary.toNat)
    (domain : post.memaddrs = state.memaddrs)
    (frame : ∀ watched : BitVec 64, watched.toNat < boundary.toNat → post.memory watched = state.memory watched) :
    RlpSliceInputPrefix post array input inputLength count.toNat := by
  have fits : array.toNat + count.toNat * 16 ≤ 2^64 := by have limit := boundary.isLt; omega
  intro index inside
  obtain ⟨pointer,length,entry⟩ := valid index inside
  have cell0 := rlpSlice_cell_toNat array index count 0 inside (by decide) fits
  have cell8 := rlpSlice_cell_toNat array index count 8 inside (by decide) fits
  have zeroAdd : array + index * 16#64 + BitVec.ofNat 64 0 = array + index * 16#64 := BitVec.add_zero _
  rw [zeroAdd] at cell0
  refine ⟨pointer,length,RlpSliceInputEntry.after_frame state post array index pointer length input inputLength entry domain ?_ ?_⟩
  · apply frame
    rw [cell0]
    omega
  · apply frame
    rw [cell8]
    omega

#print axioms rlp_slice_input_prefix_after_lower_frame
#print axioms evaluate_transaction_memzero_lower_frame
end InitECandidate.Runtime
