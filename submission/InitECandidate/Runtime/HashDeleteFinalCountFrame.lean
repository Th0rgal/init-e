import InitECandidate.Runtime.HashDeleteCountTail
import InitECandidate.Runtime.HashReverseWordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The final swap/count writes change no occupancy byte. -/
theorem hashDelete_final_writes_occupancy {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos used capacity items deletedPosition lastSlot : BitVec 64)
    (separate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + deletedPosition * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + lastSlot * 8 ∧ panByteAlignHOL (used + slot) ≠ table + 24) :
    ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead (sourceWriteWord
        (if deletedPosition = items - 1 then state else
          sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot)
            (orderPos + lastSlot * 8) deletedPosition) (table + 24) (items - 1)) used slot =
      hashOccupancyRead state used slot := by
  intro slot inside
  have facts : panByteAlignHOL (used + slot) ≠ order + deletedPosition * 8#64 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + lastSlot * 8#64 ∧
      panByteAlignHOL (used + slot) ≠ table + 24#64 := separate slot inside
  classical
  split <;> simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,facts.1,facts.2.1,facts.2.2]

/-- Actual count-tail evaluation writes the decremented header and preserves occupancy. -/
theorem evaluate_hashDelete_count_tail_count_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos deletedPosition items lastSlot used capacity : BitVec 64)
    (tableLocal : state.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (countDomain : state.memaddrs (table + 24)) (countCell : state.memory (table + 24) = .word items)
    (loadDomain : state.memaddrs (order + (items - 1) * 8))
    (loadCell : state.memory (order + (items - 1) * 8) = .word lastSlot)
    (orderDomain : state.memaddrs (order + deletedPosition * 8))
    (reverseDomain : state.memaddrs (orderPos + lastSlot * 8))
    (separate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + deletedPosition * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + lastSlot * 8 ∧ panByteAlignHOL (used + slot) ≠ table + 24) :
    ∃ post, evaluateHOLFiniteState state hashDeleteCountTail = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (items - 1) ∧
      (∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead post used slot = hashOccupancyRead state used slot) ∧
      post.clock = state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,ticks,_,code,domain,endian,memory,_⟩ := evaluate_hashDelete_count_tail state
    table order orderPos deletedPosition items lastSlot tableLocal orderLocal reverseLocal deletedLocal
    countDomain countCell loadDomain loadCell orderDomain reverseDomain
  refine ⟨post,run,?_,?_,ticks,code,domain,endian⟩
  · rw [memory]
    simp [sourceWriteWord]
  · intro slot inside
    have frame := hashDelete_final_writes_occupancy state table order orderPos used capacity items deletedPosition lastSlot separate slot inside
    unfold hashOccupancyRead at *
    rw [memory,domain,endian]
    classical
    by_cases same : deletedPosition = items - 1 <;> simp only [same,if_pos,if_neg,sourceWriteWord] at frame ⊢ <;> exact frame

#print axioms hashDelete_final_writes_occupancy
#print axioms evaluate_hashDelete_count_tail_count_frame
end InitECandidate.Runtime
