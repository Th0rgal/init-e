import InitECandidate.Runtime.HtabTxBridge
import InitECandidate.Runtime.HtabMergeWhole
import InitECandidate.Runtime.TransactionRegistryWorld
import InitECandidate.Runtime.HashTableValuesIn
import Mathlib.Data.Finset.Card
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem finset_filter_range_card (n : Nat) (p : Nat → Bool) :
    ((Finset.range n).filter (fun i => p i = true)).card = (List.range n).countP p := by
  rw [List.countP_eq_length_filter]
  simp [Finset.card,Finset.filter,Finset.range,Multiset.range,Multiset.filter]

/-- Linked order entries with the occupancy count: every live order position names an occupied slot
(the occupied slots inject into the positions below the count, and both sets have that size). -/
theorem HashOrderLinked.order_occupied_slot {F : Type} {s : PanSemStateFiniteExact 64 F}
    {used order orderPos capacity items : BitVec 64} (linked : HashOrderLinked used order orderPos capacity items s)
    (agreement : items.toNat = hashOccupiedCount capacity (hashOccupancyRead s used)) (k : BitVec 64)
    (hk : k.toNat < items.toNat) :
    ∃ slot : BitVec 64, slot.toNat < capacity.toNat ∧ hashOccupancyRead s used slot ≠ some 0 ∧
      s.memory (order + k * 8) = .word slot := by
  classical
  let S := (Finset.range capacity.toNat).filter
    (fun i => (hashOccupancyRead s used (BitVec.ofNat 64 i) != some 0) = true)
  have card : S.card = items.toNat := by
    rw [finset_filter_range_card,agreement]; rfl
  have memS : ∀ i, i ∈ S → i < capacity.toNat ∧ hashOccupancyRead s used (BitVec.ofNat 64 i) ≠ some 0 := by
    intro i h
    simp only [S,Finset.mem_filter,Finset.mem_range,bne_iff_ne,ne_eq] at h
    exact h
  have capLt : capacity.toNat < 2 ^ 64 := capacity.isLt
  have ofLt : ∀ i, i < capacity.toNat → (BitVec.ofNat 64 i).toNat < capacity.toNat := by
    intro i h; rw [BitVec.toNat_ofNat]; omega
  have pick : ∀ i (h : i ∈ S), ∃ position : BitVec 64, position.toNat < items.toNat ∧
      s.memory (orderPos + BitVec.ofNat 64 i * 8) = .word position ∧
      s.memory (order + position * 8) = .word (BitVec.ofNat 64 i) := fun i h =>
    linked _ (ofLt i (memS i h).1) (memS i h).2
  let f : (i : Nat) → i ∈ S → Nat := fun i h => (Classical.choose (pick i h)).toNat
  have onto := Finset.surj_on_of_inj_on_of_card_le (t := Finset.range items.toNat) f
    (fun i h => Finset.mem_range.mpr (Classical.choose_spec (pick i h)).1)
    (fun i j hi hj e => by
      have si := (Classical.choose_spec (pick i hi)).2.2
      have sj := (Classical.choose_spec (pick j hj)).2.2
      have pe : Classical.choose (pick i hi) = Classical.choose (pick j hj) := BitVec.eq_of_toNat_eq e
      rw [pe,sj] at si
      simp only [HolWordLab.word.injEq] at si
      have := congrArg BitVec.toNat si
      rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat] at this
      have := (memS i hi).1; have := (memS j hj).1
      omega)
    (by rw [Finset.card_range,card])
  obtain ⟨i,hi,e⟩ := onto k.toNat (Finset.mem_range.mpr hk)
  have spec := (Classical.choose_spec (pick i hi)).2.2
  have pe : Classical.choose (pick i hi) = k := BitVec.eq_of_toNat_eq e.symm
  rw [pe] at spec
  exact ⟨BitVec.ofNat 64 i,ofLt i (memS i hi).1,(memS i hi).2,spec⟩

#print axioms HashOrderLinked.order_occupied_slot

/-- Every registered table header is 8-aligned. A property of the registry set alone: it holds for the
fresh-transaction field registry and survives `insert` of a new `htab_new` table, whose header is the aligned
heap pointer (`TransactionRegistryWorld.new_table` takes exactly that alignment premise). -/
def RegistryAligned (tables : Set (BitVec 64)) : Prop := ∀ t ∈ tables, t.toNat % 8 = 0

theorem RegistryAligned.fieldRegistry {fieldPointer : BitVec 64} (fieldAligned : fieldPointer.toNat % 8 = 0) :
    RegistryAligned (stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅) :=
  stateFreshTx_registry_aligned stateFreshTxAllTables fieldPointer ∅ fieldAligned (fun _ h => False.elim h)

theorem RegistryAligned.constructed (pointer : BitVec 64) :
    RegistryAligned (stateFreshTxRegistryAfter (allocationEnd pointer 72) stateFreshTxAllTables ∅) :=
  RegistryAligned.fieldRegistry (allocationEnd_aligned pointer 72)

theorem RegistryAligned.insert {tables : Set (BitVec 64)} (h : RegistryAligned tables) {pointer : BitVec 64}
    (aligned : pointer.toNat % 8 = 0) : RegistryAligned (insert pointer tables) := by
  intro t mem
  rcases mem with rfl | mem
  · exact aligned
  · exact h t mem

/-- A registered table of the transaction registry world, in the aligned form, with its order links and value
words. -/
theorem TransactionRegistryWorld.table_ready {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {fieldPointer ts journal snapshot count : BitVec 64} {s : PanSemStateFiniteExact 64 F}
    (world : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count s)
    (al : RegistryAligned tables) (t : BitVec 64) (mem : t ∈ tables) :
    ∃ (keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat),
      HtabAligned (widths t) t keys stride capacity used values order orderPos items bits s ∧
      OrderInv s capacity items used order orderPos ∧ items.toNat < capacity.toNat ∧ stride.toNat ≤ 56 ∧
      HashOrderLinked used order orderPos capacity items s ∧ HashValueEntriesWord used values capacity s := by
  obtain ⟨_,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,sb,_⟩ := world.journalWorld.world.ready t mem
  obtain ⟨inv,tables',room⟩ := ready.toAligned (al t mem)
  exact ⟨keys,stride,capacity,used,values,order,orderPos,items,bits,
    inv.congr (r := s) rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl),
    tables'.congr (Nat.le_of_lt room) (r := s) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl),room,sb,
    ready.linked,ready.valuesWord⟩

#print axioms TransactionRegistryWorld.table_ready

/-- The words of every registered table's block `[table, orderPos + capacity * 8)`. -/
def TxTableFoot {F : Type} (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (s : PanSemStateFiniteExact 64 F) (w : Nat) : Prop :=
  ∃ t ∈ tables, ∃ (keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat),
    HtabAligned (widths t) t keys stride capacity used values order orderPos items bits s ∧
    t.toNat ≤ w ∧ w < orderPos.toNat + capacity.toNat * 8

theorem idx8_toNat (base k : BitVec 64) (h : base.toNat + k.toNat * 8 < 2 ^ 64) :
    (base + k * 8).toNat = base.toNat + k.toNat * 8 := by
  rw [BitVec.toNat_add,BitVec.toNat_mul]
  have : (8 : BitVec 64).toNat = 8 := rfl
  rw [this,Nat.mod_eq_of_lt (by omega : k.toNat * 8 < 2 ^ 64)]
  exact Nat.mod_eq_of_lt h

theorem off_toNat (base : BitVec 64) (k : Nat) (h : base.toNat + k < 2 ^ 64) (hk : k < 2 ^ 64) :
    (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hk]
  exact Nat.mod_eq_of_lt h

/-- A registered table is a merge source table for any context whose count bound covers the clamp and whose
outer footprint covers the registered blocks. -/
theorem TransactionRegistryWorld.srcTab {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {fieldPointer ts journal snapshot count : BitVec 64} {s : PanSemStateFiniteExact 64 F}
    (world : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count s)
    (al : RegistryAligned tables) (c : MergeCtx) (hNS : 4225761187 ≤ c.NS)
    (foot : ∀ w, TxTableFoot widths tables s w → c.OFoot w) (v : BitVec 64) (mem : v ∈ tables) : c.SrcTab s v := by
  obtain ⟨keys,stride,capacity,used,values,order,orderPos,items,bits,inv,tables',room,_,_,_⟩ := world.table_ready al v mem
  have hk := inv.headerKeys; have hv := inv.headerValues; have kb := inv.keysBefore; have vb := inv.valuesBefore
  have ub := inv.usedBefore; have ob := inv.orderBefore; have eb := inv.endBound
  have : keys.toNat ≤ keys.toNat + capacity.toNat * stride.toNat := Nat.le_add_right _ _
  refine ⟨widths v,keys,stride,capacity,used,values,order,orderPos,items,bits,inv.toRegions,tables',by omega,
    fun w h => foot w ⟨v,mem,keys,stride,capacity,used,values,order,orderPos,items,bits,inv,?_⟩⟩
  unfold HtabFoot at h
  omega

#print axioms TransactionRegistryWorld.srcTab

set_option maxHeartbeats 2000000 in
/-- The transaction storage map as the merge loop's outer map, from the registry world: a registered table whose
values lie in a registered target set. Its header words and count are read from its cells; every live order
position names an occupied slot, whose value word is a registered table and hence a source table. -/
theorem TransactionRegistryWorld.outer_ok {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {fieldPointer ts journal snapshot count : BitVec 64} {s : PanSemStateFiniteExact 64 F}
    (world : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count s)
    (al : RegistryAligned tables) (O : BitVec 64) (memO : O ∈ tables) (targets : Set (BitVec 64))
    (valuesIn : HashTableValuesIn O targets s) (sub : targets ⊆ tables) :
    ∃ n okeys ostride ovals oorder : BitVec 64, s.memaddrs (O + 24) ∧ s.memory (O + 24) = .word n ∧
      TxTableFoot widths tables s (O + 24).toNat ∧
      ∀ c : MergeCtx, c.O = O → c.n = n → c.okeys = okeys → c.ostride = ostride → c.ovals = ovals →
        c.oorder = oorder → 4225761187 ≤ c.NS → (∀ w, TxTableFoot widths tables s w → c.OFoot w) → c.OuterOK s := by
  obtain ⟨keys,stride,capacity,used,values,order,orderPos,items,bits,inv,_,room,_,linked,vword⟩ :=
    world.table_ready al O memO
  have hk := inv.headerKeys; have hv := inv.headerValues; have kb := inv.keysBefore; have vb := inv.valuesBefore
  have ub := inv.usedBefore; have ob := inv.orderBefore; have eb := inv.endBound
  have : keys.toNat ≤ keys.toNat + capacity.toNat * stride.toNat := Nat.le_add_right _ _
  have dom := world.journalWorld.heapDomain
  have inO : ∀ w, O.toNat ≤ w → w < orderPos.toNat + capacity.toNat * 8 → TxTableFoot widths tables s w :=
    fun w h1 h2 => ⟨O,memO,keys,stride,capacity,used,values,order,orderPos,items,bits,inv,h1,h2⟩
  have hdr : ∀ k : Nat, k < 72 → (O + BitVec.ofNat 64 k).toNat = O.toNat + k := fun k hk' =>
    off_toNat O k (by omega) (by omega)
  have c24 : (O + 24).toNat = O.toNat + 24 := hdr 24 (by omega)
  refine ⟨items,keys,stride,values,order,dom _ (by omega),inv.cell24,inO _ (by omega) (by omega),?_⟩
  intro c eO en ek es ev eo hNS foot
  subst eO
  have c56 : (c.O + 56).toNat = c.O.toNat + 56 := hdr 56 (by omega)
  have c32 : (c.O + 32).toNat = c.O.toNat + 32 := hdr 32 (by omega)
  have c8 : (c.O + 8).toNat = c.O.toNat + 8 := hdr 8 (by omega)
  have c40 : (c.O + 40).toNat = c.O.toNat + 40 := hdr 40 (by omega)
  refine ⟨⟨dom _ (by omega),by rw [eo]; exact inv.cell56,foot _ (inO _ (by omega) (by omega))⟩,
    ⟨dom _ (by omega),by rw [ek]; exact inv.cell32,foot _ (inO _ (by omega) (by omega))⟩,
    ⟨dom _ (by omega),by rw [es]; exact inv.cell8,foot _ (inO _ (by omega) (by omega))⟩,
    ⟨dom _ (by omega),by rw [ev]; exact inv.cell40,foot _ (inO _ (by omega) (by omega))⟩,fun k hk' => ?_⟩
  rw [en] at hk'
  obtain ⟨slot,slt,occ,cellO⟩ := linked.order_occupied_slot inv.agreement k hk'
  obtain ⟨u,cellV⟩ := vword slot slt occ
  have kO : (order + k * 8).toNat = order.toNat + k.toNat * 8 := idx8_toNat _ _ (by omega)
  have kV : (values + slot * 8).toNat = values.toNat + slot.toNat * 8 := idx8_toNat _ _ (by omega)
  have uT : u ∈ tables := sub (valuesIn capacity used values inv.cell16 inv.cell48 inv.cell40 slot slt occ u cellV)
  rw [eo,ev]
  exact ⟨slot,u,dom _ (by omega),cellO,foot _ (inO _ (by omega) (by omega)),dom _ (by omega),cellV,
    foot _ (inO _ (by omega) (by omega)),world.srcTab al c hNS foot u uT⟩

#print axioms TransactionRegistryWorld.outer_ok

/-- A transaction field (offset < 72) as a union source, from the registry world: its record cell holds a
registered table, which satisfies the source invariant with the order invariant, and whose block lies in the
registered footprint. -/
theorem TransactionRegistryWorld.field_source {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {fieldPointer ts journal snapshot count : BitVec 64} {s : PanSemStateFiniteExact 64 F}
    (world : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count s)
    (al : RegistryAligned tables) (offset : Nat) (table : BitVec 64)
    (binding : (offset,table) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables) (small : offset < 72) :
    s.memaddrs (ts + BitVec.ofNat 64 offset) ∧ s.memory (ts + BitVec.ofNat 64 offset) = .word table ∧ table ∈ tables ∧
      ∃ (keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat),
        HtabRegions (widths table) table keys stride capacity used values order orderPos items bits s ∧
        OrderInv s capacity items used order orderPos ∧ items.toNat < capacity.toNat ∧
        ∀ w, table.toNat ≤ w → w < orderPos.toNat + capacity.toNat * 8 → TxTableFoot widths tables s w := by
  have mem := world.fieldRegistry (stateFreshTx_binding_registered stateFreshTxAllTables fieldPointer ∅ (offset,table) binding)
  have tsB := world.tsBound
  refine ⟨world.journalWorld.heapDomain _ (by rw [off_toNat ts offset (by omega) (by omega)]; omega),
    world.fields (offset,table) binding,mem,?_⟩
  obtain ⟨keys,stride,capacity,used,values,order,orderPos,items,bits,inv,tables',room,_,_,_⟩ := world.table_ready al table mem
  exact ⟨keys,stride,capacity,used,values,order,orderPos,items,bits,inv.toRegions,tables',room,
    fun w h1 h2 => ⟨table,mem,keys,stride,capacity,used,values,order,orderPos,items,bits,inv,h1,h2⟩⟩

#print axioms TransactionRegistryWorld.field_source
end InitECandidate.Runtime
