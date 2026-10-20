import InitECandidate.Runtime.HashInsertIndexLinkedWidth
import InitECandidate.Runtime.PtKeyULeafKUGD
import InitECandidate.Runtime.HashInsertProbeTailKU
import InitECandidate.Runtime.HashInsertCopyMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderedMemoryKU
import InitECandidate.Runtime.HashInsertProbeMemoryKU
import InitECandidate.Runtime.HashInsertCopyBoundsKU
import InitECandidate.Runtime.HashInsertProbeArraysMemoryKU
import InitECandidate.Runtime.HashInsertIndexMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderEntriesKU
import InitECandidate.Runtime.HashInsertCopyOrderedEntriesKU
import InitECandidate.Runtime.HashInsertCopyEntriesKU
import InitECandidate.Runtime.HashInsertCopyLinkedWidthKU
import InitECandidate.Runtime.HashInsertProbeLinkedWidthKU
/-! Unaligned-key copy of `HashInsertIndexLinkedWidth` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Index initialization and scope restoration preserve the insertion guarantees. -/
theorem evaluate_hashInsert_index_linked_widthKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count hash keys stride key keyLength : BitVec 64) (bits : Nat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (budget : capacity.toNat + keyLength.toNat + 1 ≤ state.clock)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (sourceAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (linked : HashOrderLinked used order orderPos capacity count state) :
    ∃ post, evaluateHOLFiniteState state hashInsertIndexScope =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧
      HashOrderLinked used order orderPos capacity (count + 1) post := by
  let index := hashFindInitialIndex hash capacity
  let entered := setVarHOLFinite (ofString "i") (.val (.word index)) state
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have i : entered.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredInvariant := invariant.after_read state entered keyLength table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  obtain ⟨post,run,cost,remaining,postLinked⟩ :=
    evaluate_hashInsert_probe_linked_widthKU entered capacity used table values value order orderPos count index keys stride key keyLength bits
      ((other _ (by decide)).trans tableLocal) ((other _ (by decide)).trans orderLocal)
      ((other _ (by decide)).trans orderPosLocal) ((other _ (by decide)).trans valueLocal)
      i ((other _ (by decide)).trans capacityLocal) ((other _ (by decide)).trans usedLocal)
      ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
      ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans lengthLocal)
      (hashFind_initial_index_bound hash capacity bits invariant.power).2 budget enteredInvariant sourceAligned len8 keyFit
      sourceWordDomain sourceByteDomain
      (linked.after_read state entered used order orderPos capacity count rfl rfl rfl)
  unfold hashInsertIndexScope
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_hashFind_initial_index state hash capacity hashLocal capacityLocal]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word index))) = true := by simp [shapeOfHOLExact,shapeEqHOL]
  rw [if_pos shapeOk,run]
  refine ⟨_,rfl,cost,remaining,?_⟩
  exact postLinked.after_read post _ used order orderPos capacity (count + 1) rfl rfl rfl

#print axioms evaluate_hashInsert_index_linked_widthKU
end InitECandidate.Runtime
