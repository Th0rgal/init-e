import InitECandidate.Runtime.NodedbLoopInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A watched word at or beyond a nonwrapping byte window cannot be written by
that window, including stores to the aligned word containing a byte. -/
theorem mwin_below {D w : BitVec 64} {N : Nat} (afterWindow : D.toNat + N ≤ w.toNat) : ¬ MWin D N w := by
  rintro ⟨j,inside,equal | equal⟩
  · have natural := word_add_toNat D j (by have := w.isLt; omega)
    rw [← equal] at natural
    omega
  · have natural := word_add_toNat D j (by have := w.isLt; omega)
    have aligned := panByteAlign_toNat64 (D + BitVec.ofNat 64 j)
    rw [natural,← equal] at aligned
    have := Nat.div_mul_le_self (D.toNat + j) 8
    omega

/-- The concrete input array lying above all hash write buffers and below the
fresh database table discharges both table and future-slice separation. -/
theorem nodedb_geometry_of_intervals (c : NodedbLoopConfig)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (count : BitVec 64)
    (inv : HtabAligned 32 c.table c.keys c.stride c.capacity c.used c.values c.order c.orderPos count c.bits s)
    (small : c.total.toNat ≤ 134217712) (capacitySmall : c.capacity.toNat ≤ 536870912)
    (margin : 2 * c.total.toNat + 2 ≤ c.capacity.toNat) (outputAligned : c.output.toNat % 8 = 0)
    (arrayEnd : c.array.toNat + c.total.toNat * 16 ≤ c.table.toNat)
    (stateEnd : c.pointer.toNat + 200 ≤ c.array.toNat)
    (padEnd : c.pad.toNat + 136 ≤ c.array.toNat)
    (outputEnd : c.output.toNat + 32 ≤ c.array.toNat) : NodedbLoopGeometry c := by
  refine ⟨small,capacitySmall,margin,outputAligned,?_,?_⟩
  · intro w foot
    have lower : c.table.toNat ≤ w.toNat := by
      have := inv.headerKeys; have := inv.keysBefore; have := inv.usedBefore; have := inv.orderBefore
      unfold HtabFoot at foot
      omega
    exact ⟨mwin_below (by omega),mwin_below (by omega),mwin_below (by omega)⟩
  · intro j inside
    have first : (c.array + j * (16#64)).toNat = c.array.toNat + j.toNat * 16 :=
      word_mul_add_toNat c.array j (16#64) (by change c.array.toNat + j.toNat * 16 < 2^64; have := c.table.isLt; omega)
    have second : (c.array + j * (16#64) + (8#64)).toNat = c.array.toNat + j.toNat * 16 + 8 := by
      rw [word_add_toNat _ 8 (by rw [first]; have := c.table.isLt; omega),first]
    have retained (w : BitVec 64) (lower : c.array.toNat ≤ w.toNat) (upper : w.toNat < c.table.toNat) :
        NodedbProtected c w :=
      ⟨upper,mwin_below (by omega),mwin_below (by omega),mwin_below (by omega)⟩
    exact ⟨retained _ (by rw [first]; omega) (by rw [first]; omega),
      retained _ (by rw [second]; omega) (by rw [second]; omega)⟩

#print axioms mwin_below
#print axioms nodedb_geometry_of_intervals
end InitECandidate.Runtime
