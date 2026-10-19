import InitECandidate.Runtime.TxRegistryBridge
import InitECandidate.Runtime.FreshTxTables
import InitECandidate.Runtime.HtabBlockInit
/-!
Registry establishment including the block pre-state read table (`bs + 72`). `TabReady` (readiness without stride
and capacity bounds) and `regT_of_ready'` (the bridge over it); `rollbackReady_after` (a ready table stays ready
across a step keeping its region, with a non-decreasing heap). `stateFreshTx_regT9`: the actual original
`state_fresh_tx` call with the block table ready at entry below the entry heap gives the nine-table `RegT` at the exit
heap. `rollbackReady_of_empty` and `bs72_ready_of_built`: the table built by the original `state_init` block segment
(`BlockBuilt … blockTablesLast`) is ready in any later state keeping its block and cell — the entry premise for the first
transaction.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A table ready at some heap frontier (the readiness part of `RollbackTableReady`, without its stride and capacity
bounds). -/
def TabReady {F : Type} (widths : BitVec 64 → BitVec 64) (T : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ P K SD C U V O OP N : BitVec 64, ∃ b : Nat, HashTableReady (widths T) T K SD C U V O OP N b P s

theorem TabReady.of_rollback {F : Type} {widths : BitVec 64 → BitVec 64} {T : BitVec 64}
    {s : PanSemStateFiniteExact 64 F} (h : RollbackTableReady widths T s) : TabReady widths T s := by
  obtain ⟨P,K,SD,C,U,V,O,OP,N,b,rd,_⟩ := h
  exact ⟨P,K,SD,C,U,V,O,OP,N,b,rd⟩

/-- Bridge from the established ready-table world: `n` tables, each ready (`TabReady`) at the live heap
pointer `H`, pairwise physically separated, with pointer cells holding them, outside every table footprint and below
`H`, and an outside set `Out` below `H` off every footprint, form the content-carrying registry `RegT` (for any `ko`)
on the state's own memory, domain and endianness. -/
theorem regT_of_ready' {F : Type} (s : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) {n : Nat}
    (c T : Fin n → BitVec 64) (ko : Fin n) (H : BitVec 64)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (ready : ∀ i, TabReady widths (T i) s) (aligned : ∀ i, (T i).toNat % 8 = 0)
    (sep : ∀ i j, i ≠ j → ∀ x, rollbackTableFootprint widths (T i) s x → ¬ rollbackTableFootprint widths (T j) s x)
    (cells : ∀ i, s.memory (c i) = .word (T i))
    (cellOut : ∀ i j, ¬ rollbackTableFootprint widths (T j) s (c i) ∧ (c i).toNat < H.toNat)
    (Out : BitVec 64 → Prop)
    (hOut : ∀ x, Out x → x.toNat < H.toNat ∧ ∀ j, ¬ rollbackTableFootprint widths (T j) s x) :
    RegT n c T Out H s.memory s.memaddrs s.be ko := by
  choose P K SD C U V O OP N b hr using ready
  let l : Fin n → TLay := fun i => ⟨widths (T i),SD i,C i,N i,K i,V i,U i,O i,OP i,b i⟩
  have hP : ∀ i, P i = H := fun i => by
    have := (hr i).live.frontier.heap
    rw [heap] at this; simpa using this.symm
  have al : ∀ i, HtabAligned (widths (T i)) (T i) (K i) (SD i) (C i) (U i) (V i) (O i) (OP i) (N i) (b i) s ∧
      OrderInv s (C i) (N i) (U i) (O i) (OP i) ∧ (N i).toNat < (C i).toNat := fun i => (hr i).toAligned (aligned i)
  have front : ∀ i, (OP i).toNat + (C i).toNat * 8 ≤ H.toNat := fun i => by
    have := (hr i).live.frontier.allocated; rw [hP] at this; exact this
  -- the physical region of table `i` is its footprint, and lies below the heap
  have physFoot : ∀ i x, InTabF (T i) (K i) (SD i) (C i) (U i) (V i) (O i) (OP i) x →
      rollbackTableFootprint widths (T i) s x := fun i x hx =>
    ⟨P i,K i,SD i,C i,U i,V i,O i,OP i,N i,b i,(hr i),(phys_iff_intabf _ _ _ _ _ _ _ _ _).mpr hx⟩
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

#print axioms regT_of_ready'

/-- A ready table stays ready across any step keeping its physical region, code, domain and endianness, with the
heap pointer not decreasing (width function agreeing at the table). -/
theorem rollbackReady_after {F : Type} {s r : PanSemStateFiniteExact 64 F} {base widths : BitVec 64 → BitVec 64}
    {T P H : BitVec 64} (ready : RollbackTableReady base T s) (hw : widths T = base T)
    (sheap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word P)))
    (rheap : r.globals.lookup (ofString "heap_ptr") = some (.val (.word H))) (le : P.toNat ≤ H.toNat)
    (bound : H.toNat ≤ 33806089496) (al : H.toNat % 8 = 0)
    (frame : ∀ x, rollbackTableFootprint base T s x → r.memory x = s.memory x)
    (code : r.code = s.code) (domain : r.memaddrs = s.memaddrs) (endian : r.be = s.be) :
    RollbackTableReady widths T r := by
  obtain ⟨P',K,SD,C,U,V,O,OP,N,b,rd,sb,lc⟩ := ready
  have eP : P' = P := by have := rd.live.frontier.heap; rw [sheap] at this; simpa using this.symm
  subst eP
  let X : PanSemStateFiniteExact 64 F := { r with globals := s.globals }
  have rdX := rd.physical_frame s X _ _ _ _ _ _ _ _ _ _ _ _
    (fun x hx => frame x ⟨P',K,SD,C,U,V,O,OP,N,b,rd,hx⟩) rfl code domain endian
  have fr := rd.live.frontier.allocated
  refine ⟨H,K,SD,C,U,V,O,OP,N,b,?_,sb,lc⟩
  rw [hw]
  exact ⟨⟨rdX.live.arrays.after_read X r _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl,
    rdX.live.entries.after_memory X r _ _ _ rfl,⟨rheap,by omega,bound,al⟩⟩,
    rdX.valuesWord.after_read X r _ _ _ rfl rfl rfl,rdX.reverse.after_read X r _ _ _ _ rfl rfl rfl,
    rdX.linked.after_read X r _ _ _ _ _ rfl rfl rfl,rdX.ordering⟩

#print axioms rollbackReady_after

/-- Cells of the nine-table registry: the eight transaction tables, then the block pre-state read table's cell. -/
def c9 (ts p bsC : BitVec 64) : Fin 9 → BitVec 64 := Fin.lastCases bsC (fun j => txCell ts p j)

/-- Tables of the nine-table registry. -/
def T9 (p T72 : BitVec 64) : Fin 9 → BitVec 64 := Fin.lastCases T72 (fun j => txTab p j)

theorem c9_last (ts p bsC : BitVec 64) : c9 ts p bsC (Fin.last 8) = bsC := by unfold c9; exact Fin.lastCases_last
theorem c9_cast (ts p bsC : BitVec 64) (j : Fin 8) : c9 ts p bsC j.castSucc = txCell ts p j := by
  unfold c9; exact Fin.lastCases_castSucc j
theorem T9_last (p T72 : BitVec 64) : T9 p T72 (Fin.last 8) = T72 := by unfold T9; exact Fin.lastCases_last
theorem T9_cast (p T72 : BitVec 64) (j : Fin 8) : T9 p T72 j.castSucc = txTab p j := by
  unfold T9; exact Fin.lastCases_castSucc j

set_option maxHeartbeats 16000000 in
/-- Registry establishment at the actual original `state_fresh_tx` call with the block pre-state read table: if the
table at cell `bsC` (the `bs + 72` record cell) is ready at entry below the entry heap, the eight new transaction
tables together with it form the content-carrying registry `RegT 9` at the exit heap (outside words: below the entry
heap and off the block table). -/
theorem stateFreshTx_regT9 {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (ticks : 380 ≤ state.clock)
    (journalAligned : journal.toNat % 8 = 0)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))))
    (bsC T72 : BitVec 64) (ready72 : TabReady base T72 state) (al72 : T72.toNat % 8 = 0)
    (cell72 : state.memory bsC = .word T72) (cellLt : bsC.toNat < T72.toNat) :
    ∃ widths post H, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      TransactionRuntimeWorld widths (allocationEnd pointer 72) pointer journal snapshot 0 post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word H)) ∧ pointer.toNat ≤ H.toNat ∧
      (∀ ko : Fin 9, RegT 9 (c9 pointer (allocationEnd pointer 72) bsC) (T9 (allocationEnd pointer 72) T72)
        (fun x => x.toNat < pointer.toNat ∧ ¬ rollbackTableFootprint widths T72 post x) H post.memory post.memaddrs
        post.be ko) ∧
      state.clock ≤ post.clock + 338 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals := by
  obtain ⟨widths,post,run,world,cost,remaining,locals,agree⟩ := evaluate_stateFreshTx_transaction_runtime_world state
    base pointer oldTs bs journal snapshot oldCount code heap tsGlobal bsGlobal journalGlobal counterGlobal reservation
    journalBefore domain (by omega) journalAligned capacityGlobal
  obtain ⟨post',run',memKeep,_,ma,mb,mc,_⟩ := stateFreshTx_call_tables state pointer oldTs bs oldCount code heap tsGlobal
    bsGlobal counterGlobal reservation domain ticks
  have same : post' = post := congrArg Prod.snd (run'.symm.trans run)
  subst same
  obtain ⟨_,_,budget⟩ := stateFreshTx_reservation pointer reservation
  set p := allocationEnd pointer 72 with hp
  have cov := allocationEnd_covers pointer (72 : BitVec 64) (by change pointer.toNat + 72 ≤ _; omega)
  rw [← hp] at cov
  have e72 : (72 : BitVec 64).toNat = 72 := rfl
  rw [e72] at cov
  -- the block table at entry: below the entry heap
  obtain ⟨P0,K,SD,C,U,V,O,OP,N,b,rd⟩ := ready72
  have eP : pointer = P0 := by have := rd.live.frontier.heap; rw [heap] at this; simpa using this
  subst eP
  have a72 := rd.live.arrays
  have f72 := rd.live.frontier.allocated
  have hk := a72.headerKeys; have hv := a72.headerValues; have kb := a72.keysBefore; have vb := a72.valuesBefore
  have ub := a72.usedBefore; have ob := a72.orderBefore
  have hw72 : widths T72 = base T72 := agree T72 (by have := cov.1; have := f72; omega)
  -- the exit heap pointer
  have reg0 : txTab p 0 ∈ stateFreshTxRegistryAfter p stateFreshTxAllTables ∅ :=
    stateFreshTx_binding_registered stateFreshTxAllTables _ ∅ _ (txIdx_mem _ 0)
  obtain ⟨H,K0,SD0,C0,U0,V0,O0,OP0,N0,b0,rd0,_⟩ := world.journalWorld.world.ready _ reg0
  have fr0 := rd0.live.frontier
  have hH : post'.globals.lookup (ofString "heap_ptr") = some (.val (.word H)) := fr0.heap
  have a0 := rd0.live.arrays
  have hdr0 := world.tableHeaders _ reg0
  have := fr0.allocated; have := a0.headerKeys; have := a0.keysBefore; have := a0.usedBefore; have := a0.orderBefore
  have pH : pointer.toNat ≤ H.toNat := by omega
  -- the block table at exit
  let X : PanSemStateFiniteExact 64 F := { post' with globals := state.globals }
  have rdX := rd.physical_frame state X _ _ _ _ _ _ _ _ _ _ _ _
    (fun x hx => memKeep x (by
      rcases hx with h | h | h | h | h | h <;> omega)) rfl mc ma mb
  have rdP : HashTableReady (widths T72) T72 K SD C U V O OP N b H post' := by
    rw [hw72]
    exact ⟨⟨rdX.live.arrays.after_read X post' _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl,
      rdX.live.entries.after_memory X post' _ _ _ rfl,⟨hH,by omega,fr0.bounded,fr0.aligned⟩⟩,
      rdX.valuesWord.after_read X post' _ _ _ rfl rfl rfl,rdX.reverse.after_read X post' _ _ _ _ rfl rfl rfl,
      rdX.linked.after_read X post' _ _ _ _ _ rfl rfl rfl,rdX.ordering⟩
  have fp72 : ∀ x, rollbackTableFootprint widths T72 post' x → T72.toNat ≤ x.toNat ∧ x.toNat < pointer.toNat := by
    rintro x ⟨P',K',SD',C',U',V',O',OP',N',b',rd',ph⟩
    have eq := rd'.physical_region_eq post' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rdP
    rw [eq] at ph
    rcases ph with h | h | h | h | h | h <;> omega
  -- the transaction tables at exit lie above the entry heap
  have tsB := world.tsBound
  have reg : ∀ j, txTab p j ∈ stateFreshTxRegistryAfter p stateFreshTxAllTables ∅ := fun j =>
    stateFreshTx_binding_registered stateFreshTxAllTables p ∅ (txIdx p j) (txIdx_mem p j)
  have offs : ∀ j, (txIdx p j).1 < 72 := fun j =>
    (stateFreshTx_bindings_ge stateFreshTxAllTables p stateFreshTx_all_literals
      (by rw [stateFreshTx_all_budgets.1]; exact budget) _ (txIdx_mem p j)).2
  have cellNat : ∀ j, (txCell pointer p j).toNat = pointer.toNat + (txIdx p j).1 := fun j => by
    have := offs j
    unfold txCell
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have above : ∀ t x, rollbackTableFootprint widths t post' x → t.toNat ≤ x.toNat := by
    rintro t x ⟨P',K',SD',C',U',V',O',OP',N',b',rd',ph⟩
    have a' := rd'.live.arrays
    have := a'.headerKeys; have := a'.headerValues; have := a'.keysBefore; have := a'.valuesBefore
    have := a'.usedBefore; have := a'.orderBefore
    rcases ph with h | h | h | h | h | h <;> omega
  have tsFoot : ∀ j x, rollbackTableFootprint widths (txTab p j) post' x → pointer.toNat + 72 ≤ x.toNat := fun j x h => by
    have := above _ _ h; have := world.tableHeaders _ (reg j); omega
  have tabLt : ∀ j, (txTab p j).toNat < H.toNat := by
    intro j
    obtain ⟨P',K',SD',C',U',V',O',OP',N',b',rd',_⟩ := world.journalWorld.world.ready _ (reg j)
    have e : P' = H := by
      have h1 : post'.globals.lookup (ofString "heap_ptr") = some (.val (.word P')) := rd'.live.frontier.heap
      rw [hH] at h1; simpa using h1.symm
    have := rd'.live.frontier.allocated; rw [e] at this
    have a' := rd'.live.arrays
    have := a'.headerKeys; have := a'.keysBefore; have := a'.usedBefore; have := a'.orderBefore
    omega
  have ready9 : ∀ i, TabReady widths (T9 p T72 i) post' := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [T9_last]; exact ⟨H,K,SD,C,U,V,O,OP,N,b,rdP⟩
    · rw [T9_cast]; exact TabReady.of_rollback ((world.journalWorld.world.ready _ (reg j)).after_read rfl rfl rfl rfl rfl)
  refine ⟨widths,post',H,run,world,hH,pH,fun ko => regT_of_ready' post' widths (c9 pointer p bsC) (T9 p T72) ko H hH
    ready9 ?_ ?_ ?_ ?_ _ ?_,cost,remaining,locals⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [T9_last]; exact al72
    · rw [T9_cast]
      exact stateFreshTx_registry_aligned stateFreshTxAllTables p ∅ (allocationEnd_aligned pointer 72)
        (fun t h => False.elim h) _ (reg j)
  · intro i j ne x hx
    revert ne hx
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
    · intro ne; exact absurd rfl ne
    · intro _ hx hy; rw [T9_last] at hx; rw [T9_cast] at hy
      have := (fp72 x hx).2; have := tsFoot j' x hy; omega
    · intro _ hx hy; rw [T9_cast] at hx; rw [T9_last] at hy
      have := (fp72 x hy).2; have := tsFoot i' x hx; omega
    · intro ne hx; rw [T9_cast] at hx ⊢
      exact world.journalWorld.separated _ (reg i') _ (reg j')
        (fun e => ne (by rw [txTab_inj p budget e])) x hx
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [c9_last,T9_last,memKeep bsC (by omega)]; exact cell72
    · rw [c9_cast,T9_cast]; exact world.fields (txIdx p j) (txIdx_mem p j)
  · intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
    · rw [c9_last,T9_last]
      exact ⟨fun hf => by have := (fp72 _ hf).1; omega,by omega⟩
    · rw [c9_last,T9_cast]
      exact ⟨fun hf => by have := tsFoot j' _ hf; omega,by omega⟩
    · rw [c9_cast,T9_last]
      exact ⟨fun hf => by have := (fp72 _ hf).2; have := cellNat i'; omega,
        by have := world.tableHeaders _ (reg i'); have := cellNat i'; have := offs i'; have := tabLt i'; omega⟩
    · rw [c9_cast,T9_cast]
      exact ⟨fun hf => by
          have := above _ _ hf; have := world.tableHeaders _ (reg j'); have := cellNat i'; have := offs i'; omega,
        by have := world.tableHeaders _ (reg i'); have := cellNat i'; have := offs i'; have := tabLt i'; omega⟩
  · intro x ⟨hlt,hnot⟩
    refine ⟨by omega,fun j => ?_⟩
    revert j
    intro j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · rw [T9_last]; exact hnot
    · rw [T9_cast]; exact fun hf => by have := tsFoot j' x hf; omega

#print axioms stateFreshTx_regT9
/-- An empty aligned table with the full heap domain and the heap pointer above its arrays is ready. -/
theorem rollbackReady_of_empty {F : Type} (s : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64)
    {T K SD C U V O OP P : BitVec 64} {b : Nat}
    (inv : HtabAligned (widths T) T K SD C U V O OP 0 b s) (oi : OrderInv s C 0 U O OP)
    (kv : K.toNat + C.toNat * SD.toNat ≤ V.toNat)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word P)))
    (front : OP.toNat + C.toNat * 8 ≤ P.toNat) (bound : P.toNat ≤ 33806089496) (al : P.toNat % 8 = 0)
    : TabReady widths T s := by
  have zero : hashOccupiedCount C (hashOccupancyRead s U) = 0 := by rw [← inv.agreement]; rfl
  have zeroed := hashOccupiedCount_zero_reads C (hashOccupancyRead s U) zero
  have eb := inv.endBound
  refine ⟨P,K,SD,C,U,V,O,OP,0,b,⟨⟨⟨inv.code,inv.power,inv.keysAligned,inv.strideAligned,inv.valuesAligned,
    inv.usedAligned,inv.orderAligned,inv.orderPosAligned,inv.headerKeys,inv.headerValues,inv.keysBefore,
    inv.valuesBefore,inv.usedBefore,inv.orderBefore,inv.endBound,inv.fits,fun a _ h => domain a (by omega),inv.cell0,
    inv.cell8,inv.cell16,inv.cell24,inv.cell32,inv.cell40,inv.cell48,inv.cell56,inv.cell64,inv.agreement,
    by have := inv.power; have : 0 < 2 ^ b := Nat.two_pow_pos b; simp; omega⟩,oi.2,⟨heap,front,bound,al⟩⟩,
    HashValueEntriesWord.empty s U V C zeroed,
    HashReverseEntriesBound.empty s U OP C zeroed,HashOrderLinked.empty s U O OP C zero,kv⟩⟩

#print axioms rollbackReady_of_empty

/-- The block pre-state read table built by the original `state_init` block segment (`bs + 72`, key width 20,
capacity 256) is ready in any later state keeping its block `[lo, hi)` and its cell, with the full heap domain and the
heap pointer at least `hi`. -/
theorem bs72_ready_of_built {F G : Type} {B : BitVec 64} {s : PanSemStateFiniteExact 64 F}
    {r : PanSemStateFiniteExact 64 G} {lo hi : Nat} (built : BlockBuilt B blockTablesLast s lo hi)
    (widths : BitVec 64 → BitVec 64)
    (ma : r.memaddrs = s.memaddrs) (mb : r.be = s.be) (mc : r.code = s.code)
    (keep : ∀ a : BitVec 64, lo ≤ a.toNat → a.toNat < hi → r.memory a = s.memory a)
    (cellKeep : r.memory (B + BitVec.ofNat 64 72) = s.memory (B + BitVec.ofNat 64 72))
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → r.memaddrs a) (P : BitVec 64)
    (heap : r.globals.lookup (ofString "heap_ptr") = some (.val (.word P))) (hiP : hi ≤ P.toNat)
    (bound : P.toNat ≤ 33806089496) (al : P.toNat % 8 = 0) :
    ∃ T : BitVec 64, r.memory (B + BitVec.ofNat 64 72) = .word T ∧ lo ≤ T.toNat ∧ T.toNat % 8 = 0 ∧
      ((∀ a, widths a = 20) → TabReady widths T r) := by
  have rb := BlockBuilt.keep blockTablesLast s r lo hi built ma mb mc keep
    (fun o m => by simp [blockTablesLast] at m; subst m; exact cellKeep)
  obtain ⟨T,K,SD,U,V,O,OP,b,cell,inv,kv,oi,pw,lt,fr⟩ := BlockBuilt.entry blockTablesLast r lo hi rb 20 256 72 (by simp [blockTablesLast])
  refine ⟨T,cell,lt,inv.tableAligned,fun hw => ?_⟩
  have e20 : widths T = BitVec.ofNat 64 20 := by rw [hw]; rfl
  rw [← e20] at inv
  exact rollbackReady_of_empty r widths inv oi kv domain heap (le_trans fr hiP) bound al

#print axioms bs72_ready_of_built
end InitECandidate.Runtime
