import InitECandidate.Runtime.PtTabRVGD
/-!
The layout of a ready table (root's `HashTableReady`) as the heap-layout facts of the `htab_set` frame contract: a
table ready at the heap pointer `H` has the canonical layout `HLay H T (Canon …)` with its header in memory, its arrays
inside its physical region below `H`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section rh
/-- A ready table at heap pointer `H` (aligned header) has the canonical heap layout at `H` and its header. -/
theorem ready_hlay {F : Type} {s : PanSemStateFiniteExact 64 F} {KL T K SD C U V O OP N H : BitVec 64} {b : Nat}
    (rd : HashTableReady KL T K SD C U V O OP N b H s) (aligned : T.toNat % 8 = 0) :
    HLay H T (Canon T C SD K V U O OP H) KL SD C N K V U O OP b ∧ Hdr s.memory T KL SD C N K V U O OP ∧
      ∀ x, InTabF T K SD C U V O OP x → x.toNat < H.toNat := by
  obtain ⟨inv,_,room⟩ := rd.toAligned aligned
  have front : OP.toNat + C.toNat * 8 ≤ H.toNat := rd.live.frontier.allocated
  have := inv.headerKeys; have := inv.headerValues; have := inv.keysBefore
  have := inv.valuesBefore; have := inv.usedBefore; have := inv.orderBefore; have := inv.endBound
  refine ⟨⟨inv.power,inv.fits,inv.strideAligned,inv.keysAligned,inv.usedAligned,room,fun x lo hi => Or.inl ⟨lo,hi⟩,
      by omega,by omega,fun x hx => Or.inr (Or.inr hx),
      ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inl ⟨lo,hi⟩))⟩,
      ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inl ⟨lo,hi⟩)))⟩,
      ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨lo,hi⟩))))⟩,
      ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨lo,hi⟩)))))⟩,
      ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨lo,hi⟩)))))⟩⟩,
    ⟨inv.cell0,inv.cell8,inv.cell16,inv.cell24,inv.cell32,inv.cell40,inv.cell48,inv.cell56,inv.cell64⟩,
    fun x hx => ?_⟩
  rcases hx with h | h | h | h | h | h <;> omega

#print axioms ready_hlay
end rh
end InitECandidate.Runtime
