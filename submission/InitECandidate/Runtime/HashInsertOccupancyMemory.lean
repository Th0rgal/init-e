import InitECandidate.Runtime.HashInsertCountMemory
import InitECandidate.Runtime.HashInsertCountInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact occupancy and bookkeeping stores preserve runtime metadata and
any word distinct from their four destination cells. -/
theorem evaluate_hashInsert_occupancy_count_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used table order orderPos count index cell : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteDomain : state.memaddrs (panByteAlignHOL (used + index)))
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell)
    (orderDomain : state.memaddrs (order + count * 8))
    (orderPosDomain : state.memaddrs (orderPos + index * 8))
    (countDomain : state.memaddrs (table + 24))
    (countMemory : state.memory (table + 24) = .word count)
    (countSeparate : table + 24 ≠ panByteAlignHOL (used + index)) :
    ∃ post, evaluateHOLFiniteState state (.seq hashInsertOccupancyStore hashInsertCountTail) =
        (some (.returned (.val (.word 0))),post) ∧
      post.memory = (sourceWriteWord (sourceWriteWord (sourceWriteWord
        (sourceWriteByte state (used + index) 1 cell) (order + count * 8) index)
        (orderPos + index * 8) count) (table + 24) (count + 1)).memory ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64, watched ≠ panByteAlignHOL (used + index) →
        watched ≠ order + count * 8 → watched ≠ orderPos + index * 8 → watched ≠ table + 24 →
        post.memory watched = state.memory watched := by
  let marked := sourceWriteByte state (used + index) 1 cell
  have store : evaluateHOLFiniteState state hashInsertOccupancyStore = (none,marked) := by
    apply evaluate_source_storeByte
    · simp [evalHOLExact,evalListHOLExact,usedLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    · rfl
    · exact byteDomain
    · exact byteMemory
  have headerAfter : marked.memory (table + 24) = .word count :=
    (sourceWriteByte_memory_other state (used + index) 1 cell (table + 24) countSeparate).trans countMemory
  obtain ⟨post,tail,memory,clock,globals,code,addresses,endian,frame⟩ := evaluate_hashInsert_count_tail_memory marked
    table order orderPos count index tableLocal orderLocal orderPosLocal indexLocal
    orderDomain orderPosDomain countDomain headerAfter
  refine ⟨post,evaluate_seq_none store tail,memory,clock,globals,code,addresses,endian,?_⟩
  intro watched byte first second third
  exact (frame watched first second third).trans
    (sourceWriteByte_memory_other state (used + index) 1 cell watched byte)

#print axioms evaluate_hashInsert_occupancy_count_memory
end InitECandidate.Runtime
