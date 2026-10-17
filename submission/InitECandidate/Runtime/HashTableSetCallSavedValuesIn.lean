import InitECandidate.Runtime.HashTableReadySetCallRecordFrameSupported
import InitECandidate.Runtime.HashTableReadySetUnsafeGrowthCallFrameDichotomy
import InitECandidate.Runtime.JournalSavedValuesIn
import InitECandidate.Runtime.JournalUndoRecordIntervals
import InitECandidate.Runtime.HashTableValuesInSetCallNoGrowth
import InitECandidate.Runtime.HashTableValuesInSetNoGrowth
import InitECandidate.Runtime.HashTableArraysFindSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_call_saved_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initialReady : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56)
    (ticks : 2 ^ 74 ≤ state.clock)
    (domain : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride) → ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))     (journal : BitVec 64) (journalCount : Nat) (watched targets : Set (BitVec 64))
    (saved : JournalSavedValuesIn journal journalCount watched targets state)
    (journalBefore : journal.toNat + journalCount * 32 ≤ table.toNat)
    (journalBound : journal.toNat + journalCount * 32 ≤ 33806089496)
    (success : (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 = none) :
    JournalSavedValuesIn journal journalCount watched targets
      (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2 := by
  have u := initialReady.live.arrays.usedBefore
  have o := initialReady.live.arrays.orderBefore
  have e := initialReady.live.arrays.endBound
  have room := initialReady.live.arrays.room
  have capBound : capacity.toNat ≤ 33806089496 := by omega
  have keyBound : keyLength.toNat ≤ 52 := by rcases supported with h | h | h <;> simp [h]
  have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
    rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
    change capacity.toNat * 2 = 2 * capacity.toNat
    omega
  have product := Nat.mul_le_mul (show items.toNat ≤ 33806089496 by omega)
    (show (capacity * (2 : BitVec 64)).toNat + keyLength.toNat + 4 ≤ 67612179048 by rw [doubled]; omega)
  have bound : 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 13 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ 2 ^ 74 := by rw [doubled]; rw [doubled] at product; omega
  let call : ProgHOL 64 := .call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]
  have hk := initialReady.live.arrays.headerKeys
  have hv := initialReady.live.arrays.headerValues
  have ku := initialReady.live.arrays.keysBefore
  have vu := initialReady.live.arrays.valuesBefore
  have uo := initialReady.live.arrays.usedBefore
  have oo := initialReady.live.arrays.orderBefore
  have allocated := initialReady.live.frontier.allocated
  have preservePhysical (post : PanSemStateFiniteExact 64 F)
      (frame : ∀ address : BitVec 64, ¬tablePhysicalRegion table keys stride capacity used values order orderPos address → post.memory address = state.memory address) :
      JournalSavedValuesIn journal journalCount watched targets post := by
    apply saved.after_frame (Nat.le_refl _)
    intro index inside offset belongs
    have offsetBound : offset < 32 := by simp at belongs; omega
    have interval := journal_undo_field_interval journal journalCount index offset journalBound inside offsetBound
    apply frame
    unfold tablePhysicalRegion
    omega
  by_cases safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)
  · obtain ⟨post,run,_,_,_,_,_,_,_,frame⟩ := initialReady.set_call_supported_record_frame state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
      strideBound initialReady.live.frontier.aligned initialReady.live.frontier.bounded capBound safe (by omega) initialReady.live.frontier.heap (domain safe)
      tableArgument keyArgument valueArgument arguments capacityLarge keyAligned sourceWordDomain sourceByteDomain journal journalCount (by omega) (by omega) (by omega) (Or.inl journalBefore)
    rw [run]
    exact saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; exact frame index inside offset (by simp at belongs ⊢; omega))
  · by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
    · obtain ⟨nextCount,post,_,run,_,_,frame,_⟩ := initialReady.set_call_no_growth_values_in state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        keyAligned sourceWordDomain sourceByteDomain below (by omega) tableArgument keyArgument valueArgument arguments Set.univ
        (by intro capacity used values _ _ _ slot _ _ value _; trivial) (by trivial)
      rw [run]
      exact preservePhysical post frame
    · have outcome := initialReady.set_unsafe_growth_call_frame_dichotomy state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain (by omega) initialReady.live.frontier.heap initialReady.live.frontier.bounded safe (by omega)
      rcases outcome with good | failed
      · obtain ⟨post,run,_,_,_,_,_,_,_,_,frame⟩ := good
        rw [run]
        exact preservePhysical post frame
      · exact False.elim (failed.1 success)

#print axioms HashTableReady.set_call_saved_values_in
end InitECandidate.Runtime
