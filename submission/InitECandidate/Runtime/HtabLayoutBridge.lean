import InitECandidate.Runtime.PreStateAccountArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The existing aligned-table invariant gives the arena layout (table region `[T, orderPos + 8 cap)`) and the
header cells, once the count is below capacity and the header lies below fresh heap. -/
theorem hlay_of_aligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (P0 : BitVec 64) (cnt : count.toNat < capacity.toNat) (below : table.toNat + 72 ≤ P0.toNat) :
    HLay P0 table (orderPos + capacity * 8#64) keyLength stride capacity count keys values used order orderPos bits ∧
      Hdr s.memory table keyLength stride capacity count keys values used order orderPos ∧
      (orderPos + capacity * 8#64).toNat = orderPos.toNat + capacity.toNat * 8 := by
  have eB := inv.endBound
  have eE : (orderPos + capacity * 8#64).toNat = orderPos.toNat + capacity.toNat * 8 :=
    toNat_add_mul8 orderPos capacity (by omega)
  have hk := inv.headerKeys; have hv := inv.headerValues; have kb := inv.keysBefore; have vb := inv.valuesBefore
  have ub := inv.usedBefore; have ob := inv.orderBefore
  refine ⟨⟨inv.power,inv.fits,inv.strideAligned,inv.keysAligned,inv.usedAligned,cnt,by omega,below,by omega,
      Or.inl ⟨hk,by omega⟩,Or.inl ⟨hv,by omega⟩,Or.inl ⟨by omega,by omega⟩,Or.inl ⟨by omega,by omega⟩,
      Or.inl ⟨by omega,by omega⟩⟩,
    ⟨inv.cell0,inv.cell8,inv.cell16,inv.cell24,inv.cell32,inv.cell40,inv.cell48,inv.cell56,inv.cell64⟩,eE⟩

#print axioms hlay_of_aligned
end InitECandidate.Runtime
