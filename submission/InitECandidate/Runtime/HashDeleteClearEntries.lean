import InitECandidate.Runtime.HashDeleteClearCount
import InitECandidate.Runtime.HashValueEntriesWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A zero byte store cannot make a previously empty slot occupied. -/
theorem sourceWriteByte_clear_occupied_before {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used erased cell slot : BitVec 64)
    (domain : state.memaddrs (panByteAlignHOL (used + erased)))
    (memory : state.memory (panByteAlignHOL (used + erased)) = .word cell)
    (occupied : hashOccupancyRead (sourceWriteByte state (used + erased) 0 cell) used slot ≠ some 0) :
    hashOccupancyRead state used slot ≠ some 0 := by
  by_cases same : slot = erased
  · subst slot
    exact False.elim (occupied (sourceWriteByte_load_self state (used + erased) 0 cell domain))
  · have different : used + slot ≠ used + erased := by simpa using same
    have unchanged := sourceWriteByte_load_other state (used + erased) 0 cell (used + slot) different memory
    change hashOccupancyRead (sourceWriteByte state (used + erased) 0 cell) used slot = hashOccupancyRead state used slot at unchanged
    rw [← unchanged]
    exact occupied

theorem hashDelete_clear_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used values orderPos capacity items erased cell : BitVec 64)
    (domain : state.memaddrs (panByteAlignHOL (used + erased)))
    (memory : state.memory (panByteAlignHOL (used + erased)) = .word cell)
    (words : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (valuesSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ panByteAlignHOL (used + erased))
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → orderPos + slot * 8 ≠ panByteAlignHOL (used + erased)) :
    HashValueEntriesWord used values capacity (sourceWriteByte state (used + erased) 0 cell) ∧
      HashReverseEntriesBound used orderPos capacity items (sourceWriteByte state (used + erased) 0 cell) := by
  constructor
  · intro slot inside occupied
    obtain ⟨value,word⟩ := words slot inside (sourceWriteByte_clear_occupied_before state used erased cell slot domain memory occupied)
    exact ⟨value,(sourceWriteByte_memory_other state (used + erased) 0 cell (values + slot * 8) (valuesSeparate slot inside)).trans word⟩
  · intro slot inside occupied
    obtain ⟨position,word,bound⟩ := reverse slot inside (sourceWriteByte_clear_occupied_before state used erased cell slot domain memory occupied)
    exact ⟨position,(sourceWriteByte_memory_other state (used + erased) 0 cell (orderPos + slot * 8) (reverseSeparate slot inside)).trans word,bound⟩

#print axioms sourceWriteByte_clear_occupied_before
#print axioms hashDelete_clear_entries
end InitECandidate.Runtime
