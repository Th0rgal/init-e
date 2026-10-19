import InitECandidate.Runtime.HtabUnionSites
import InitECandidate.Runtime.TransactionRuntimeWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem allocationEnd_aligned (pointer size : BitVec 64) : (allocationEnd pointer size).toNat % 8 = 0 := by
  rw [allocationEnd_eq_align]
  unfold panByteAlignHOL
  have l : (64 / 8 : Nat).log2 = 3 := by decide
  rw [l,BitVec.toNat_ofNat]
  omega

#print axioms allocationEnd_aligned

/-- A ready table (full-byte domain) with an 8-aligned header is an aligned table with the order invariant and room. -/
theorem HashTableReady.toAligned {F : Type} {keyLength table keys stride capacity used values order orderPos count : BitVec 64}
    {bits : Nat} {pointer : BitVec 64} {s : PanSemStateFiniteExact 64 F}
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer s)
    (tableAligned : table.toNat % 8 = 0) :
    HtabAligned keyLength table keys stride capacity used values order orderPos count bits s ∧
      OrderInv s capacity count used order orderPos ∧ count.toNat < capacity.toNat := by
  have a := ready.live.arrays
  refine ⟨⟨a.code,a.power,tableAligned,a.keysAligned,a.strideAligned,a.valuesAligned,a.usedAligned,a.orderAligned,
      a.orderPosAligned,a.headerKeys,a.headerValues,a.keysBefore,a.valuesBefore,a.usedBefore,a.orderBefore,a.endBound,
      a.fits,fun x _ h1 h2 => a.domain x h1 h2,a.cell0,a.cell8,a.cell16,a.cell24,a.cell32,a.cell40,a.cell48,a.cell56,
      a.cell64,a.agreement⟩,⟨fun q lt occ => ?_,ready.live.entries⟩,a.room⟩
  obtain ⟨x,cell,xlt⟩ := ready.reverse q lt occ
  exact ⟨x,cell,Nat.lt_trans xlt a.room⟩

#print axioms HashTableReady.toAligned

/-- Every fresh-transaction constructor table address is 8-aligned when the first one is. -/
theorem stateFreshTx_registry_aligned (specs : List (Nat × Nat × Nat)) :
    ∀ (pointer : BitVec 64) (tables : Set (BitVec 64)), pointer.toNat % 8 = 0 → (∀ t ∈ tables, t.toNat % 8 = 0) →
      ∀ t ∈ stateFreshTxRegistryAfter pointer specs tables, t.toNat % 8 = 0 := by
  induction specs with
  | nil => intro pointer tables _ h; exact h
  | cons spec rest ih =>
    rcases spec with ⟨width,capacity,offset⟩
    intro pointer tables pa h
    refine ih _ _ (allocationEnd_aligned _ _) ?_
    intro t mem
    rcases mem with rfl | mem
    · exact pa
    · exact h t mem

#print axioms stateFreshTx_registry_aligned

/-- A transaction-state field table, from the recurrent transaction world: its record cell, and the table as
an aligned table with the order invariant and room, plus its stride bound (with an aligned field frontier,
which the constructor provides as `allocationEnd pointer 72`). -/
theorem TransactionRuntimeWorld.field_aligned {F : Type} {widths : BitVec 64 → BitVec 64}
    {fieldPointer ts journal snapshot count : BitVec 64} {s : PanSemStateFiniteExact 64 F}
    (world : TransactionRuntimeWorld widths fieldPointer ts journal snapshot count s)
    (fieldAligned : fieldPointer.toNat % 8 = 0) (offset : Nat) (table : BitVec 64)
    (binding : (offset,table) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables) (small : offset < 72) :
    s.memaddrs (ts + BitVec.ofNat 64 offset) ∧ s.memory (ts + BitVec.ofNat 64 offset) = .word table ∧
      table ∈ stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅ ∧
      ∃ (keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat),
        HtabAligned (widths table) table keys stride capacity used values order orderPos items bits s ∧
        OrderInv s capacity items used order orderPos ∧ items.toNat < capacity.toNat ∧ stride.toNat ≤ 56 := by
  have mem := stateFreshTx_binding_registered stateFreshTxAllTables fieldPointer ∅ (offset,table) binding
  have tsB := world.tsBound
  have addr : (ts + BitVec.ofNat 64 offset).toNat = ts.toNat + offset := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
  refine ⟨world.journalWorld.heapDomain _ (by omega),world.fields (offset,table) binding,mem,?_⟩
  obtain ⟨_,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,sb,_⟩ :=
    world.journalWorld.world.ready table mem
  have ta := stateFreshTx_registry_aligned stateFreshTxAllTables fieldPointer ∅ fieldAligned
    (fun t h => False.elim h) table mem
  obtain ⟨inv,tables,room⟩ := ready.toAligned ta
  exact ⟨keys,stride,capacity,used,values,order,orderPos,items,bits,
    inv.congr (r := s) rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl),
    tables.congr (Nat.le_of_lt room) (r := s) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl),room,sb⟩

#print axioms TransactionRuntimeWorld.field_aligned
end InitECandidate.Runtime
