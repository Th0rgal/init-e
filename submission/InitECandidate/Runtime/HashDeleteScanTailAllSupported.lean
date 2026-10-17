import InitECandidate.Runtime.HashDeleteLinkedLoopLocalSupported
import InitECandidate.Runtime.HashDeleteFinalTailAllEntriesWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original scan and final suffix return with live linkage for the
smaller table, within 55 clocks per slot. -/
theorem evaluate_hashDelete_scan_tail_all_supported {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat * 55 ≤ state.clock)
    (deletedBound : deletedPosition.toNat < items.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition))) :
    ∃ post, evaluateHOLFiniteState state (.seq hashDeleteLoop hashDeleteFinalTail) =
      (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock ∧
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos (items - 1) bits post ∧
      HashValueEntriesWord used values capacity post ∧ HashOrderEntriesBound order capacity (items - 1) post ∧
      HashReverseEntriesBound used orderPos capacity (items - 1) post ∧ HashOrderLinked used order orderPos capacity (items - 1) post := by
  obtain ⟨scanned,scanRun,exitValid,cost,remaining,tFrame⟩ := evaluate_hashDelete_linked_loop_local_supported
    keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state valid supported budget
    (ofString "t") (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨checked,checkedRun,_,_,_,deletedFrame⟩ := evaluate_hashDelete_linked_loop_local_supported
    keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state valid supported budget
    (ofString "deleted_pos") (by decide) (by decide) (by decide) (by decide) (by decide)
  have same : scanned = checked := congrArg Prod.snd (scanRun.symm.trans checkedRun)
  have saved : scanned.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)) := by
    rw [same,deletedFrame]
    exact deletedLocal
  obtain ⟨base,hole,holeLocal,linked⟩ := exitValid
  obtain ⟨actualHole,index,holeInside,_,actualLocal,_,actualOccupied⟩ := base.indices
  have holeSame : actualHole = hole := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actualLocal.symm.trans holeLocal
  have inside : hole.toNat < capacity.toNat := by simpa [holeSame] using holeInside
  have holeOccupied : hashOccupancyRead scanned used hole ≠ some 0 := by simpa [holeSame] using actualOccupied
  obtain ⟨post,tail,ticks,arrays,words,orderEntries,reverseEntries,postLinked⟩ := evaluate_hashDelete_final_tail_all_entries_width scanned
    keyLength table keys stride capacity used values order orderPos items hole deletedPosition bits base.arrays linked base.valuesWord holeOccupied inside deletedBound base.ordered
    (tFrame.trans tableLocal) base.orderLocal base.reverseLocal saved base.usedLocal holeLocal
  refine ⟨post,?_,by omega,by omega,arrays,words,orderEntries,reverseEntries,postLinked⟩
  rw [evaluateHOLFiniteState_seq_line780,scanRun]
  exact tail

#print axioms evaluate_hashDelete_scan_tail_all_supported
end InitECandidate.Runtime
