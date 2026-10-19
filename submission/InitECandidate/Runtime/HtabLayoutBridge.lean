import InitECandidate.Runtime.PreStateAccountArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The interval footprint of an aligned table: its region `[T, orderPos + 8 cap)` and fresh heap. -/
def tabFoot (P0 table orderPos capacity : BitVec 64) (x : BitVec 64) : Prop :=
  (table.toNat ≤ x.toNat ∧ x.toNat < orderPos.toNat + capacity.toNat * 8) ∨ P0.toNat ≤ x.toNat

/-- The existing aligned-table invariant gives the arena layout for any footprint `E` containing the table region
`[T, orderPos + 8 cap)` and fresh heap, and the header cells, once the count is below capacity and the header lies
below fresh heap. -/
theorem hlay_of_aligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (P0 : BitVec 64) (E : BitVec 64 → Prop)
    (hE : ∀ x : BitVec 64, table.toNat ≤ x.toNat → x.toNat < orderPos.toNat + capacity.toNat * 8 → E x)
    (hF : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → E x)
    (cnt : count.toNat < capacity.toNat) (below : table.toNat + 72 ≤ P0.toNat) :
    HLay P0 table E keyLength stride capacity count keys values used order orderPos bits ∧
      Hdr s.memory table keyLength stride capacity count keys values used order orderPos := by
  have eB := inv.endBound
  have hk := inv.headerKeys; have hv := inv.headerValues; have kb := inv.keysBefore; have vb := inv.valuesBefore
  have ub := inv.usedBefore; have ob := inv.orderBefore
  refine ⟨⟨inv.power,inv.fits,inv.strideAligned,inv.keysAligned,inv.usedAligned,cnt,
      fun x lo hi => hE x lo (by omega),below,by omega,hF,
      ⟨hk,by omega,fun x lo hi => hE x (by omega) (by omega)⟩,⟨hv,by omega,fun x lo hi => hE x (by omega) (by omega)⟩,
      ⟨by omega,by omega,fun x lo hi => hE x (by omega) (by omega)⟩,
      ⟨by omega,by omega,fun x lo hi => hE x (by omega) (by omega)⟩,
      ⟨by omega,by omega,fun x lo hi => hE x (by omega) (by omega)⟩⟩,
    ⟨inv.cell0,inv.cell8,inv.cell16,inv.cell24,inv.cell32,inv.cell40,inv.cell48,inv.cell56,inv.cell64⟩⟩

#print axioms hlay_of_aligned
end InitECandidate.Runtime
