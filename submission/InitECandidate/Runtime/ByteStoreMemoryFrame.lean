import InitECandidate.Runtime.ByteStoresControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A byte store preserves every other aligned word, including when its value
expression or memory access fails. -/
theorem evaluate_storeByte_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (address watched : BitVec 64)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)))
    (separate : watched ≠ panByteAlignHOL address) :
    (evaluateHOLFiniteState state (.storeByte destination value)).2.memory watched = state.memory watched := by
  rw [evaluateHOLFiniteState_storeByte,addressEval]
  dsimp only
  split
  · split
    · rename_i storedMemory stored
      cases cell : state.memory (panByteAlignHOL address) with
      | word cell =>
        by_cases accessible : state.memaddrs (panByteAlignHOL address)
        · simp [panMemStoreByteWord8HOL,accessible] at stored
          rw [← stored]
          simp only [if_neg separate]
        · simp [panMemStoreByteWord8HOL,accessible] at stored
    · rfl
  · rfl

#print axioms evaluate_storeByte_memory_frame
end InitECandidate.Runtime
