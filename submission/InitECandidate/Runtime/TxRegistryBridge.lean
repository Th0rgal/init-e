import InitECandidate.Runtime.DestroyStorageGD
import InitECandidate.Runtime.HtabTxBridge
import InitECandidate.Runtime.RollbackPhysicalSeparated
import InitECandidate.Runtime.StateFreshTxRegistryLowerBound
import InitECandidate.Runtime.StateFreshTxConcretePlan
import InitECandidate.Runtime.StateFreshTxTransactionRuntimeWorld
/-!
Registry establishment for the content-carrying registry `RegT`. `regT_of_ready`: tables ready at the live heap
pointer (`RollbackTableReady`), pairwise physically separated, with pointer cells holding them off every footprint and
below the heap, form `RegT` on the state's own memory, domain and endianness. `regT_of_txWorld`: the eight transaction
tables of `TransactionRuntimeWorld` (cells `ts + 8, …, ts + 64`), given the constructor reservation at the field
frontier; distinctness from strict frontier growth (`stateFreshTx_bindings_nodup`). `stateFreshTx_regT`: the actual
original `state_fresh_tx` call establishes `RegT` (outside words: everything below the entry heap) through the existing
producer `evaluate_stateFreshTx_transaction_runtime_world`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A table's physical region is its header together with its five arrays (`InTabF`), reordered. -/
theorem phys_iff_intabf (T K SD C U V O OP x : BitVec 64) :
    tablePhysicalRegion T K SD C U V O OP x ↔ InTabF T K SD C U V O OP x := by
  unfold tablePhysicalRegion InTabF
  constructor
  · rintro (h | h | h | h | h | h)
    exacts [Or.inl h,Or.inr (Or.inl h),Or.inr (Or.inr (Or.inr (Or.inl h))),Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))),Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))]
  · rintro (h | h | h | h | h | h)
    exacts [Or.inl h,Or.inr (Or.inl h),Or.inr (Or.inr (Or.inr (Or.inl h))),Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))),Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))]

/-- Bridge from the established ready-table world: `n` tables, each ready (`RollbackTableReady`) at the live heap
pointer `H`, pairwise physically separated, with pointer cells holding them, outside every table footprint and below
`H`, and an outside set `Out` below `H` off every footprint, form the content-carrying registry `RegT` (for any `ko`)
on the state's own memory, domain and endianness. -/
theorem regT_of_ready {F : Type} (s : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) {n : Nat}
    (c T : Fin n → BitVec 64) (ko : Fin n) (H : BitVec 64)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (ready : ∀ i, RollbackTableReady widths (T i) s) (aligned : ∀ i, (T i).toNat % 8 = 0)
    (sep : ∀ i j, i ≠ j → ∀ x, rollbackTableFootprint widths (T i) s x → ¬ rollbackTableFootprint widths (T j) s x)
    (cells : ∀ i, s.memory (c i) = .word (T i))
    (cellOut : ∀ i j, ¬ rollbackTableFootprint widths (T j) s (c i) ∧ (c i).toNat < H.toNat)
    (Out : BitVec 64 → Prop)
    (hOut : ∀ x, Out x → x.toNat < H.toNat ∧ ∀ j, ¬ rollbackTableFootprint widths (T j) s x) :
    RegT n c T Out H s.memory s.memaddrs s.be ko := by
  choose P K SD C U V O OP N b hr using ready
  let l : Fin n → TLay := fun i => ⟨widths (T i),SD i,C i,N i,K i,V i,U i,O i,OP i,b i⟩
  have hP : ∀ i, P i = H := fun i => by
    have := (hr i).1.live.frontier.heap
    rw [heap] at this; simpa using this.symm
  have al : ∀ i, HtabAligned (widths (T i)) (T i) (K i) (SD i) (C i) (U i) (V i) (O i) (OP i) (N i) (b i) s ∧
      OrderInv s (C i) (N i) (U i) (O i) (OP i) ∧ (N i).toNat < (C i).toNat := fun i => (hr i).1.toAligned (aligned i)
  have front : ∀ i, (OP i).toNat + (C i).toNat * 8 ≤ H.toNat := fun i => by
    have := (hr i).1.live.frontier.allocated; rw [hP] at this; exact this
  -- the physical region of table `i` is its footprint, and lies below the heap
  have physFoot : ∀ i x, InTabF (T i) (K i) (SD i) (C i) (U i) (V i) (O i) (OP i) x →
      rollbackTableFootprint widths (T i) s x := fun i x hx =>
    ⟨P i,K i,SD i,C i,U i,V i,O i,OP i,N i,b i,(hr i).1,(phys_iff_intabf _ _ _ _ _ _ _ _ _).mpr hx⟩
  have physLt : ∀ i x, InTabF (T i) (K i) (SD i) (C i) (U i) (V i) (O i) (OP i) x → x.toNat < H.toNat := by
    intro i x hx
    obtain ⟨inv,_,_⟩ := al i
    have := front i; have := inv.headerKeys; have := inv.keysBefore; have := inv.valuesBefore
    have := inv.usedBefore; have := inv.orderBefore
    rcases hx with h | h | h | h | h | h <;> omega
  -- not in a canonical footprint at `H` whenever off the physical region and below `H`
  have offCanon : ∀ i x, ¬ rollbackTableFootprint widths (T i) s x → x.toNat < H.toNat → ¬ (l i).canon (T i) H x := by
    intro i x hf hlt hc
    rcases hc with h | h | h
    · exact hf (physFoot i x (Or.inl h))
    · exact hf (physFoot i x (Or.inr h))
    · omega
  refine ⟨l,⟨fun i => ⟨?_,offCanon i _ (cellOut i i).1 (cellOut i i).2⟩,fun i j ne x hx => ?_,
    fun x hx i => offCanon i x ((hOut x hx).2 i) (hOut x hx).1⟩,fun i => ⟨cells i,?_⟩,?_,fun x hx => ?_⟩
  · obtain ⟨inv,_,room⟩ := al i
    show HLay H (T i) (Canon (T i) (C i) (SD i) (K i) (V i) (U i) (O i) (OP i) H) (widths (T i)) (SD i) (C i) (N i)
      (K i) (V i) (U i) (O i) (OP i) (b i)
    have := front i; have := inv.headerKeys; have := inv.headerValues; have := inv.keysBefore
    have := inv.valuesBefore; have := inv.usedBefore; have := inv.orderBefore; have := inv.endBound
    exact ⟨inv.power,inv.fits,inv.strideAligned,inv.keysAligned,inv.usedAligned,room,fun x lo hi => Or.inl ⟨lo,hi⟩,
      by omega,by omega,fun x hx => Or.inr (Or.inr hx),
      ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inl ⟨lo,hi⟩))⟩,
      ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inl ⟨lo,hi⟩)))⟩,
      ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨lo,hi⟩))))⟩,
      ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨lo,hi⟩)))))⟩,
      ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨lo,hi⟩)))))⟩⟩
  · rcases hx with rfl | hx
    · exact offCanon i _ (cellOut j i).1 (cellOut j i).2
    · have inj : InTabF (T j) (K j) (SD j) (C j) (U j) (V j) (O j) (OP j) x := by
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr h
      exact offCanon i x (sep j i (Ne.symm ne) x (physFoot j x inj)) (physLt j x inj)
  · obtain ⟨inv,_,_⟩ := al i
    exact ⟨inv.cell0,inv.cell8,inv.cell16,inv.cell24,inv.cell32,inv.cell40,inv.cell48,inv.cell56,inv.cell64⟩
  · obtain ⟨inv,oi,_⟩ := al ko
    exact ⟨F,s,rfl,rfl,rfl,inv.code,inv,oi⟩
  · exact physLt ko x (Or.inr hx)

#print axioms regT_of_ready

/-- Fresh-transaction binding tables lie at or above the initial frontier. -/
theorem stateFreshTx_bindings_ge (specs : List (Nat × Nat × Nat)) :
    ∀ (pointer : BitVec 64), StateFreshTxLiterals specs →
      pointer.toNat + stateFreshTxAllocationBudget specs ≤ 33806089496 →
      ∀ b ∈ stateFreshTxTableBindings pointer specs, pointer.toNat ≤ b.2.toNat ∧ b.1 < 72 := by
  induction specs with
  | nil => intro pointer _ _ b hb; simp [stateFreshTxTableBindings] at hb
  | cons spec rest ih =>
    rcases spec with ⟨width,capacity,offset⟩
    intro pointer literals budget b hb
    obtain ⟨widthBound,capacityBound,_,offB,_,tail⟩ := literals
    have reserve : pointer.toNat + 81 * capacity + 114 + stateFreshTxAllocationBudget rest ≤ 33806089496 := by
      simpa only [stateFreshTxAllocationBudget,Nat.add_assoc] using budget
    obtain ⟨advance,upper,_⟩ := stateFreshTx_next_table_bounds pointer width capacity widthBound capacityBound (by omega)
    rcases List.mem_cons.mp hb with rfl | later
    · exact ⟨le_refl _,offB⟩
    · have := ih _ tail (by omega) b later
      exact ⟨by omega,this.2⟩

/-- Fresh-transaction binding tables are pairwise distinct. -/
theorem stateFreshTx_bindings_nodup (specs : List (Nat × Nat × Nat)) :
    ∀ (pointer : BitVec 64), StateFreshTxLiterals specs →
      pointer.toNat + stateFreshTxAllocationBudget specs ≤ 33806089496 →
      ((stateFreshTxTableBindings pointer specs).map Prod.snd).Nodup := by
  induction specs with
  | nil => intro pointer _ _; simp [stateFreshTxTableBindings]
  | cons spec rest ih =>
    rcases spec with ⟨width,capacity,offset⟩
    intro pointer literals budget
    obtain ⟨widthBound,capacityBound,_,_,_,tail⟩ := literals
    have reserve : pointer.toNat + 81 * capacity + 114 + stateFreshTxAllocationBudget rest ≤ 33806089496 := by
      simpa only [stateFreshTxAllocationBudget,Nat.add_assoc] using budget
    obtain ⟨advance,upper,_⟩ := stateFreshTx_next_table_bounds pointer width capacity widthBound capacityBound (by omega)
    simp only [stateFreshTxTableBindings,List.map_cons,List.nodup_cons]
    refine ⟨fun hm => ?_,ih _ tail (by omega)⟩
    obtain ⟨b,hb,e⟩ := List.mem_map.mp hm
    have := (stateFreshTx_bindings_ge rest _ tail (by omega) b hb).1
    rw [e] at this; omega

#print axioms stateFreshTx_bindings_nodup

/-- The eight fresh-transaction table bindings `(offset, table)` from the field frontier `p`. -/
def txBind (p : BitVec 64) : List (Nat × BitVec 64) := stateFreshTxTableBindings p stateFreshTxAllTables

theorem txBind_length (p : BitVec 64) : (txBind p).length = 8 := by
  have := congrArg List.length (stateFreshTx_table_binding_offsets p)
  simpa [txBind] using this

/-- Binding `i` (offsets `8, 16, …, 64`). -/
def txIdx (p : BitVec 64) (i : Fin 8) : Nat × BitVec 64 := (txBind p).get (Fin.cast (txBind_length p).symm i)

/-- Pointer cell `ts + offset` of transaction table `i`. -/
def txCell (ts p : BitVec 64) (i : Fin 8) : BitVec 64 := ts + BitVec.ofNat 64 (txIdx p i).1

/-- Transaction table `i`. -/
def txTab (p : BitVec 64) (i : Fin 8) : BitVec 64 := (txIdx p i).2

theorem txIdx_mem (p : BitVec 64) (i : Fin 8) : txIdx p i ∈ txBind p := List.get_mem _ _

theorem txTab_inj (p : BitVec 64) (reserve : p.toNat + 22944 ≤ 33806089496) {i j : Fin 8} (e : txTab p i = txTab p j) :
    i = j := by
  have nd := stateFreshTx_bindings_nodup stateFreshTxAllTables p stateFreshTx_all_literals
    (by rw [stateFreshTx_all_budgets.1]; exact reserve)
  have inj := List.nodup_iff_injective_get.mp nd
  have : ((txBind p).map Prod.snd).get (Fin.cast (by simp [txBind_length]) i) =
      ((txBind p).map Prod.snd).get (Fin.cast (by simp [txBind_length]) j) := by
    simp only [List.get_eq_getElem,List.getElem_map]
    exact e
  have h := inj this
  ext; simpa using congrArg Fin.val h

set_option maxHeartbeats 4000000 in
/-- The eight transaction tables of the recurrent transaction world (with the constructor reservation at the field
frontier) form the content-carrying registry `RegT` at the live heap pointer, for any of them as content table. -/
theorem regT_of_txWorld {F : Type} (s : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64)
    (p ts journal snapshot count : BitVec 64) (world : TransactionRuntimeWorld widths p ts journal snapshot count s)
    (fieldAligned : p.toNat % 8 = 0) (reserve : p.toNat + 22944 ≤ 33806089496) (H : BitVec 64)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H))) (Out : BitVec 64 → Prop)
    (hOut : ∀ x, Out x → x.toNat < H.toNat ∧
      ∀ t ∈ stateFreshTxRegistryAfter p stateFreshTxAllTables ∅, ¬ rollbackTableFootprint widths t s x)
    (ko : Fin 8) :
    RegT 8 (txCell ts p) (txTab p) Out H s.memory s.memaddrs s.be ko := by
  have reg : ∀ i, txTab p i ∈ stateFreshTxRegistryAfter p stateFreshTxAllTables ∅ := fun i =>
    stateFreshTx_binding_registered stateFreshTxAllTables p ∅ (txIdx p i) (txIdx_mem p i)
  have offs : ∀ i, (txIdx p i).1 < 72 := fun i =>
    (stateFreshTx_bindings_ge stateFreshTxAllTables p stateFreshTx_all_literals
      (by rw [stateFreshTx_all_budgets.1]; exact reserve) _ (txIdx_mem p i)).2
  have ready : ∀ i, RollbackTableReady widths (txTab p i) s := fun i =>
    (world.journalWorld.world.ready _ (reg i)).after_read rfl rfl rfl rfl rfl
  have tsB := world.tsBound
  have cellNat : ∀ i, (txCell ts p i).toNat = ts.toNat + (txIdx p i).1 := fun i => by
    have := offs i
    unfold txCell
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  -- every array of a ready table lies at or above its header end, and below the heap pointer
  have above : ∀ t x, rollbackTableFootprint widths t s x → t.toNat ≤ x.toNat := by
    rintro t x ⟨P,K,SD,C,U,V,O,OP,N,b,rd,ph⟩
    have a := rd.live.arrays
    have := a.headerKeys; have := a.headerValues; have := a.keysBefore; have := a.valuesBefore
    have := a.usedBefore; have := a.orderBefore
    rcases ph with h | h | h | h | h | h <;> omega
  have tabLt : ∀ i, (txTab p i).toNat < H.toNat := by
    intro i
    obtain ⟨P,K,SD,C,U,V,O,OP,N,b,rd,_⟩ := ready i
    have a := rd.live.arrays
    have fr := rd.live.frontier
    have e : P = H := by have := fr.heap; rw [heap] at this; simpa using this.symm
    have := fr.allocated; rw [e] at this
    have := a.headerKeys; have := a.keysBefore; have := a.usedBefore; have := a.orderBefore
    omega
  refine regT_of_ready s widths (txCell ts p) (txTab p) ko H heap ready
    (fun i => stateFreshTx_registry_aligned stateFreshTxAllTables p ∅ fieldAligned (fun t h => False.elim h) _ (reg i))
    (fun i j ne x hx => world.journalWorld.separated _ (reg i) _ (reg j) (fun e => ne (txTab_inj p reserve e)) x hx)
    (fun i => world.fields (txIdx p i) (txIdx_mem p i)) (fun i j => ⟨fun hf => ?_,?_⟩) Out
    (fun x hx => ⟨(hOut x hx).1,fun j => (hOut x hx).2 _ (reg j)⟩)
  · have := above _ _ hf; have := world.tableHeaders _ (reg j); have := cellNat i; have := offs i
    omega
  · have := world.tableHeaders _ (reg i); have := cellNat i; have := offs i; have := tabLt i
    omega

#print axioms regT_of_txWorld

theorem txCell_offsets (ts p : BitVec 64) :
    txCell ts p 0 = ts + 8 ∧ txCell ts p 1 = ts + 16#64 ∧ txCell ts p 2 = ts + 24#64 ∧ txCell ts p 3 = ts + 32#64 ∧
      txCell ts p 4 = ts + 40#64 ∧ txCell ts p 5 = ts + 48#64 ∧ txCell ts p 6 = ts + 56#64 ∧
      txCell ts p 7 = ts + 64#64 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms txCell_offsets

set_option maxHeartbeats 4000000 in
/-- Registry establishment at the actual original `state_fresh_tx` call: from heap pointer `pointer` (with the
constructor reservation and the existing producer premises), the call returns normally into the transaction world,
and the eight new transaction tables form the content-carrying registry `RegT` at the exit heap pointer, with every
word below the entry heap as an outside word, on the exit state's own memory, domain and endianness. -/
theorem stateFreshTx_regT {F : Type} (state : PanSemStateFiniteExact 64 F)
    (base : BitVec 64 → BitVec 64) (pointer oldTs bs journal snapshot oldCount : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : state.globals.lookup (ofString "bs") = some (.val (.word bs)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (counterGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (reservation : pointer.toNat + 23024 ≤ 33806089496)
    (journalBefore : journal.toNat + 524288 * 32 ≤ pointer.toNat)
    (domain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (ticks : 338 ≤ state.clock)
    (journalAligned : journal.toNat % 8 = 0)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64)))) :
    ∃ widths post H, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      TransactionRuntimeWorld widths (allocationEnd pointer 72) pointer journal snapshot 0 post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word H)) ∧ pointer.toNat ≤ H.toNat ∧
      (∀ ko : Fin 8, RegT 8 (txCell pointer (allocationEnd pointer 72)) (txTab (allocationEnd pointer 72))
        (fun x => x.toNat < pointer.toNat) H post.memory post.memaddrs post.be ko) ∧
      state.clock ≤ post.clock + 338 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals := by
  obtain ⟨widths,post,run,world,cost,remaining,locals,_⟩ := evaluate_stateFreshTx_transaction_runtime_world state base
    pointer oldTs bs journal snapshot oldCount code heap tsGlobal bsGlobal journalGlobal counterGlobal reservation
    journalBefore domain ticks journalAligned capacityGlobal
  obtain ⟨_,_,budget⟩ := stateFreshTx_reservation pointer reservation
  have reg0 : txTab (allocationEnd pointer 72) 0 ∈ stateFreshTxRegistryAfter (allocationEnd pointer 72)
      stateFreshTxAllTables ∅ :=
    stateFreshTx_binding_registered stateFreshTxAllTables _ ∅ _ (txIdx_mem _ 0)
  obtain ⟨H,K,SD,C,U,V,O,OP,N,b,rd,_⟩ := world.journalWorld.world.ready _ reg0
  have fr := rd.live.frontier
  have hH : post.globals.lookup (ofString "heap_ptr") = some (.val (.word H)) := fr.heap
  have a := rd.live.arrays
  have hdr := world.tableHeaders _ reg0
  have := fr.allocated; have := a.headerKeys; have := a.keysBefore; have := a.usedBefore; have := a.orderBefore
  have above : ∀ t x, rollbackTableFootprint widths t post x → t.toNat ≤ x.toNat := by
    rintro t x ⟨P,K',SD',C',U',V',O',OP',N',b',rd',ph⟩
    have a' := rd'.live.arrays
    have := a'.headerKeys; have := a'.headerValues; have := a'.keysBefore; have := a'.valuesBefore
    have := a'.usedBefore; have := a'.orderBefore
    rcases ph with h | h | h | h | h | h <;> omega
  refine ⟨widths,post,H,run,world,hH,by omega,fun ko => regT_of_txWorld post widths _ _ _ _ _ world
    (allocationEnd_aligned pointer 72) budget H hH _ (fun x hx => ⟨by omega,fun t ht hf => ?_⟩) ko,cost,remaining,locals⟩
  have := above _ _ hf; have := world.tableHeaders _ ht
  omega

#print axioms stateFreshTx_regT
end InitECandidate.Runtime
