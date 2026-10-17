import InitECandidate.Runtime.HashDeleteFinalTailLinked32
import InitECandidate.Runtime.HashDeleteFinalTailArrays32
import InitECandidate.Runtime.HashDeleteFinalTailWords32
import InitECandidate.Runtime.HashDeleteFinalTailOrder32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- All reusable table and entry invariants for the same actual suffix result. -/
theorem evaluate_hashDelete_final_tail_all32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (entries : HashValueEntriesWord used values capacity state)
    (ordered : HashOrderEntriesBound order capacity items state)
    (occupied : hashOccupancyRead state used hole ≠ some 0)
    (holeInside : hole.toNat < capacity.toNat) (lastInside : lastSlot.toNat < capacity.toNat)
    (positive : 0 < items.toNat) (deletedBound : deletedPosition.toNat < items.toNat)
    (cellMemory : state.memory (panByteAlignHOL (used + hole)) = .word cell)
    (lastCell : state.memory (order + (items - 1) * 8) = .word lastSlot)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole))) :
    ∃ post, evaluateHOLFiniteState state hashDeleteFinalTail = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      post.clock = state.clock ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos (items - 1) bits post ∧
      HashValueEntriesWord used values capacity post ∧
      HashOrderEntriesBound order capacity (items - 1) post ∧
      HashReverseEntriesBound used orderPos capacity (items - 1) post ∧
      HashOrderLinked used order orderPos capacity (items - 1) post := by
  obtain ⟨post,run,ticks,postLinked⟩ := evaluate_hashDelete_final_tail_linked32 state table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell bits
    invariant linked holeInside lastInside positive deletedBound cellMemory lastCell tableLocal orderLocal reverseLocal deletedLocal usedLocal holeLocal
  obtain ⟨arrayPost,arrayRun,_,arrays⟩ := evaluate_hashDelete_final_tail_arrays32 state table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell bits
    invariant occupied holeInside lastInside positive deletedBound cellMemory lastCell tableLocal orderLocal reverseLocal deletedLocal usedLocal holeLocal
  obtain ⟨wordPost,wordRun,_,words⟩ := evaluate_hashDelete_final_tail_words32 state table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell bits
    invariant entries holeInside lastInside positive deletedBound cellMemory lastCell tableLocal orderLocal reverseLocal deletedLocal usedLocal holeLocal
  obtain ⟨orderPost,orderRun,_,orderEntries⟩ := evaluate_hashDelete_final_tail_order32 state table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell bits
    invariant ordered holeInside lastInside positive deletedBound cellMemory lastCell tableLocal orderLocal reverseLocal deletedLocal usedLocal holeLocal
  have arraySame : post = arrayPost := congrArg Prod.snd (run.symm.trans arrayRun)
  have wordSame : post = wordPost := congrArg Prod.snd (run.symm.trans wordRun)
  have orderSame : post = orderPost := congrArg Prod.snd (run.symm.trans orderRun)
  refine ⟨post,run,ticks,?_,?_,?_,?_,postLinked⟩
  · rw [arraySame]; exact arrays
  · rw [wordSame]; exact words
  · rw [orderSame]; exact orderEntries
  · intro slot inside live
    obtain ⟨position,bound,reverse,_⟩ := postLinked slot inside live
    exact ⟨position,reverse,bound⟩

#print axioms evaluate_hashDelete_final_tail_all32
end InitECandidate.Runtime
