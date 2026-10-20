import InitECandidate.Runtime.PtDomAlignGD
import InitECandidate.Runtime.HashTableReady
/-!
Root's table geometry invariant `HashTableArraysInvariant` carries an interval-wide `domain` field
(`∀ a ∈ [table, orderPos + 8·cap), memaddrs a`), which includes `table` and `table + 1`.  In the actual
aligned-only domain no state satisfies it, so `HashTableReady` (and every invariant built on it) is uninhabited at
actual states.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.PanSemStateFiniteExact

theorem hashTableArraysInvariant_not_actual {F : Type}
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) (dom : state.memaddrs = ordinaryDomain) :
    ¬ HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state := by
  intro inv
  have hb := inv.headerKeys
  have hk := inv.keysBefore
  have hu := inv.usedBefore
  have ho := inv.orderBefore
  have he := inv.endBound
  have t1 : (table + 1).toNat = table.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by simp; omega)]; rfl
  have d0 := inv.domain table (le_refl _) (by omega)
  have d1 := inv.domain (table + 1) (by omega) (by omega)
  rw [dom] at d0 d1
  exact ordinaryDomain_not_consecutive table ⟨d0, d1⟩

theorem hashTableReady_not_actual {F : Type}
    (keyLength table keys stride capacity used values order orderPos items pointer : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) (dom : state.memaddrs = ordinaryDomain) :
    ¬ HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state :=
  fun r => hashTableArraysInvariant_not_actual _ _ _ _ _ _ _ _ _ _ _ state dom r.live.arrays

#print axioms hashTableArraysInvariant_not_actual
#print axioms hashTableReady_not_actual
end InitECandidate.Runtime
