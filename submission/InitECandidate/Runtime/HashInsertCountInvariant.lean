import InitECandidate.Runtime.HashInsertOccupancyStore
import InitECandidate.Runtime.HashInsertCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

open InitECandidate.Proofs.FrontendCodecComputation

def sourceFirstByteStoreSuffix : ProgHOL 64 → Option (ProgHOL 64)
  | .seq (.storeByte destination value) rest => some (.seq (.storeByte destination value) rest)
  | .dec _ _ _ body => sourceFirstByteStoreSuffix body
  | .decCall _ _ _ _ body => sourceFirstByteStoreSuffix body
  | .seq first rest => (sourceFirstByteStoreSuffix first).orElse (fun _ => sourceFirstByteStoreSuffix rest)
  | _ => none

/-- Exact adjacency of the two source fragments composed below. -/
theorem source_htabInsert_count_suffix :
    sourceFirstByteStoreSuffix (sourceFunctionBody Guest.guestFn_htab_insert_raw) =
      some (.seq hashInsertOccupancyStore hashInsertCountTail) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_htab_insert_raw,declToHOLStructural,funDeclToHOLStructural,
    progToHOLStructural,expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,
    List.map_cons,List.map_nil,Option.map_none,sourceFirstByteStoreSuffix,Option.orElse,
    hashInsertOccupancyStore,hashInsertCountTail,hashInsertCountStores,hashLocalAddress,hashOrderAddress]
  rfl

/-- The contiguous occupancy-write/count-update suffix preserves agreement
between the header's natural item count and the actual occupancy-byte count. -/
theorem evaluate_hashInsert_count_invariant {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table order orderPos count index cell : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (inside : index.toNat < capacity.toNat)
    (byteDomain : state.memaddrs (panByteAlignHOL (used + index)))
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell)
    (empty : hashOccupancyRead state used index = some 0)
    (orderDomain : state.memaddrs (order + count * 8))
    (orderPosDomain : state.memaddrs (orderPos + index * 8))
    (countDomain : state.memaddrs (table + 24))
    (countMemory : state.memory (table + 24) = .word count)
    (agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used))
    (noWrap : count.toNat + 1 < 2 ^ 64)
    (separate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + count * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + index * 8 ∧
      panByteAlignHOL (used + slot) ≠ table + 24) :
    ∃ post, evaluateHOLFiniteState state (.seq hashInsertOccupancyStore hashInsertCountTail) =
        (some (.returned (.val (.word 0))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧ post.clock = state.clock := by
  let marked := sourceWriteByte state (used + index) 1 cell
  have store : evaluateHOLFiniteState state hashInsertOccupancyStore = (none,marked) := by
    apply evaluate_source_storeByte
    · simp [evalHOLExact,evalListHOLExact,usedLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    · rfl
    · exact byteDomain
    · exact byteMemory
  have headerAfter : marked.memory (table + 24) = .word count := by
    exact (sourceWriteByte_memory_other state (used + index) 1 cell (table + 24)
      (Ne.symm (separate index inside).2.2)).trans countMemory
  obtain ⟨post,tail,header,clock,preserved⟩ := evaluate_hashInsert_count_tail marked
    table order orderPos count index tableLocal orderLocal orderPosLocal indexLocal
    orderDomain orderPosDomain countDomain headerAfter
  have countAfter := preserved capacity used separate
  have filled := sourceWriteByte_occupancy_fill state capacity used index cell inside byteDomain byteMemory empty
  have countWord : (count + 1).toNat = count.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by exact noWrap)]
    rfl
  refine ⟨post,evaluate_seq_none store tail,header,?_,clock⟩
  rw [countAfter,filled,← agreement,countWord]

#print axioms source_htabInsert_count_suffix
#print axioms evaluate_hashInsert_count_invariant
end InitECandidate.Runtime
