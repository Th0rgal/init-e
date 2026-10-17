import InitECandidate.Runtime.HashInsertProbeOrderEntries
import InitECandidate.Runtime.HashInsertCopyLinkedWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original probe and insertion preserve the live order link. -/
theorem evaluate_hashInsert_probe_linked_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count initialIndex keys stride key keyLength : BitVec 64) (bits : Nat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word initialIndex)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (inside : initialIndex.toNat < capacity.toNat)
    (budget : capacity.toNat + keyLength.toNat + 1 ≤ state.clock)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (sourceAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (linked : HashOrderLinked used order orderPos capacity count state) :
    ∃ post, evaluateHOLFiniteState state hashInsertProbeTail =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧
      HashOrderLinked used order orderPos capacity (count + 1) post := by
  change capacity.toNat + keyLength.toNat + 1 ≤ state.clock at budget
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos count bits
  have environment := facts.enter capacity used table values value order orderPos count state state
    rfl rfl rfl tableLocal orderLocal orderPosLocal usedLocal valueLocal
  have prepared := environment.prepare capacity used table values value order orderPos count state
  have readable : ∀ current : BitVec 64, current.toNat < capacity.toNat →
      ∃ byte, hashOccupancyRead state used current = some byte := by
    intro current inRange
    have available := facts.byteDomain current inRange
    unfold hashOccupancyRead panMemLoadByteHOL
    dsimp only
    rw [if_pos available]
    exact ⟨_,rfl⟩
  have room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat := by
    rw [← invariant.agreement]
    exact invariant.room
  obtain ⟨probed,slot,cell,probeRun,probeCost,probeRemaining,probeMemory,probeGlobals,probeCode,addresses,probeEndian,ready,other⟩ :=
    evaluate_hashInsert_probe_ready state capacity used table values value order orderPos count initialIndex bits invariant.power
      indexLocal capacityLocal usedLocal inside (by omega) readable room prepared
  have probedInvariant := invariant.after_read state probed keyLength table keys stride capacity used values order orderPos count bits
    probeMemory probeCode addresses probeEndian
  have probedLinked := linked.after_read state probed used order orderPos capacity count probeMemory addresses probeEndian
  obtain ⟨post,tail,cost,remaining,postLinked⟩ :=
    probedInvariant.insert_copy_linked_width probed capacity used table values value order orderPos count slot cell keys stride key keyLength bits
      probedLinked ready.tableLocal ready.orderLocal ready.orderPosLocal ready.usedLocal ready.indexLocal ready.valueLocal
      ready.inside ready.byteMemory
      ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
      ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans lengthLocal)
      sourceAligned (by omega)
      (by rw [addresses]; exact sourceWordDomain) (by rw [addresses]; exact sourceByteDomain)
  refine ⟨post,?_,by omega,by omega,postLinked⟩
  unfold hashInsertProbeTail
  rw [evaluateHOLFiniteState_seq_line780,probeRun]
  exact tail

#print axioms evaluate_hashInsert_probe_linked_width
end InitECandidate.Runtime
