import InitECandidate.Runtime.BlockRegistryBridge
/-!
Nine-table registry establishment from the block table's layout facts only, the form carried between transactions.
`regT_of_ready_snoc`: `n` ready tables plus one table given by its layout facts (valid canonical layout at the heap,
header in memory, arrays below the heap, pointer cell), mutually separated, form `RegT (n + 1)`.
`stateFreshTx_regT9L`: the actual original `state_fresh_tx` call with the block table's layout facts at the entry heap
gives `RegT 9` at the exit heap. `regT_tab_facts`: those layout facts read back from any registry.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000 in
/-- Bridge with one extra table given only by its layout facts (valid canonical layout at the heap, header in memory,
arrays below the heap, pointer cell): `n` ready tables (as in `regT_of_ready'`) and the extra table, mutually
separated, form `RegT (n + 1)` with the content of a ready table. -/
theorem regT_of_ready_snoc {F : Type} (s : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) {n : Nat}
    (c T : Fin n → BitVec 64) (ko : Fin n) (H : BitVec 64)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (ready : ∀ i, TabReady widths (T i) s) (aligned : ∀ i, (T i).toNat % 8 = 0)
    (sep : ∀ i j, i ≠ j → ∀ x, rollbackTableFootprint widths (T i) s x → ¬ rollbackTableFootprint widths (T j) s x)
    (cells : ∀ i, s.memory (c i) = .word (T i))
    (cellOut : ∀ i j, ¬ rollbackTableFootprint widths (T j) s (c i) ∧ (c i).toNat < H.toNat)
    (cB TB : BitVec 64) (lB : TLay) (okB : lB.ok TB H) (hdrB : lB.hdr s.memory TB) (cellB : s.memory cB = .word TB)
    (cBoff : ¬ lB.canon TB H cB) (arrB : ∀ x, lB.arr x → x.toNat < H.toNat)
    (extraOff : ∀ x, (x = cB ∨ HdrR TB x ∨ lB.arr x) → ∀ i, ¬ rollbackTableFootprint widths (T i) s x)
    (readyOff : ∀ i x, (x = c i ∨ rollbackTableFootprint widths (T i) s x) → ¬ lB.canon TB H x)
    (Out : BitVec 64 → Prop)
    (hOut : ∀ x, Out x → x.toNat < H.toNat ∧ (∀ j, ¬ rollbackTableFootprint widths (T j) s x) ∧ ¬ lB.canon TB H x) :
    RegT (n + 1) (Fin.lastCases cB c) (Fin.lastCases TB T) Out H s.memory s.memaddrs s.be ko.castSucc := by
  choose P K SD C U V O OP N b hr using ready
  let l : Fin n → TLay := fun i => ⟨widths (T i),SD i,C i,N i,K i,V i,U i,O i,OP i,b i⟩
  let l9 : Fin (n + 1) → TLay := Fin.lastCases lB l
  have l9l : l9 (Fin.last n) = lB := Fin.lastCases_last
  have l9c : ∀ j, l9 j.castSucc = l j := fun j => Fin.lastCases_castSucc j
  have cl : (Fin.lastCases cB c : Fin (n + 1) → BitVec 64) (Fin.last n) = cB := Fin.lastCases_last
  have cc : ∀ j, (Fin.lastCases cB c : Fin (n + 1) → BitVec 64) j.castSucc = c j := fun j => Fin.lastCases_castSucc j
  have Tl : (Fin.lastCases TB T : Fin (n + 1) → BitVec 64) (Fin.last n) = TB := Fin.lastCases_last
  have Tc : ∀ j, (Fin.lastCases TB T : Fin (n + 1) → BitVec 64) j.castSucc = T j := fun j => Fin.lastCases_castSucc j
  have hP : ∀ i, P i = H := fun i => by
    have := (hr i).live.frontier.heap
    rw [heap] at this; simpa using this.symm
  have al : ∀ i, HtabAligned (widths (T i)) (T i) (K i) (SD i) (C i) (U i) (V i) (O i) (OP i) (N i) (b i) s ∧
      OrderInv s (C i) (N i) (U i) (O i) (OP i) ∧ (N i).toNat < (C i).toNat := fun i => (hr i).toAligned (aligned i)
  have front : ∀ i, (OP i).toNat + (C i).toNat * 8 ≤ H.toNat := fun i => by
    have := (hr i).live.frontier.allocated; rw [hP] at this; exact this
  have physFoot : ∀ i x, InTabF (T i) (K i) (SD i) (C i) (U i) (V i) (O i) (OP i) x →
      rollbackTableFootprint widths (T i) s x := fun i x hx =>
    ⟨P i,K i,SD i,C i,U i,V i,O i,OP i,N i,b i,hr i,(phys_iff_intabf _ _ _ _ _ _ _ _ _).mpr hx⟩
  have physLt : ∀ i x, InTabF (T i) (K i) (SD i) (C i) (U i) (V i) (O i) (OP i) x → x.toNat < H.toNat := by
    intro i x hx
    obtain ⟨inv,_,_⟩ := al i
    have := front i; have := inv.headerKeys; have := inv.keysBefore; have := inv.valuesBefore
    have := inv.usedBefore; have := inv.orderBefore
    rcases hx with h | h | h | h | h | h <;> omega
  have offCanon : ∀ i x, ¬ rollbackTableFootprint widths (T i) s x → x.toNat < H.toNat → ¬ (l i).canon (T i) H x := by
    intro i x hf hlt hc
    rcases hc with h | h | h
    · exact hf (physFoot i x (Or.inl h))
    · exact hf (physFoot i x (Or.inr h))
    · omega
  have hdrPB := okB.hdrP
  have cBlt : cB.toNat < H.toNat := by
    by_contra h; exact cBoff (Or.inr (Or.inr (by omega)))
  have okR : ∀ i, (l i).ok (T i) H := by
    intro i
    obtain ⟨inv,_,room⟩ := al i
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
  refine ⟨l9,⟨fun i => ?_,fun i j ne x hx => ?_,fun x hx i => ?_⟩,fun i => ?_,?_,fun x hx => ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [l9l,Tl,cl]; exact ⟨okB,cBoff⟩
    · rw [l9c,Tc,cc]; exact ⟨okR j,offCanon j _ (cellOut j j).1 (cellOut j j).2⟩
  · revert ne hx
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
    · intro ne; exact absurd rfl ne
    · -- words of ready table `j'` against the extra table's canon
      intro _ hx; rw [l9l,Tl]; rw [cc,Tc,l9c] at hx
      rcases hx with rfl | hx
      · exact readyOff j' _ (Or.inl rfl)
      · have inj : InTabF (T j') (K j') (SD j') (C j') (U j') (V j') (O j') (OP j') x := by
          rcases hx with h | h
          · exact Or.inl h
          · exact Or.inr h
        exact readyOff j' x (Or.inr (physFoot j' x inj))
    · -- words of the extra table against ready table `i'`
      intro _ hx; rw [l9c,Tc]; rw [cl,Tl,l9l] at hx
      have lt : x.toNat < H.toNat := by
        rcases hx with rfl | ⟨_,h⟩ | h
        · exact cBlt
        · omega
        · exact arrB x h
      exact offCanon i' x (extraOff x hx i') lt
    · intro ne hx; rw [l9c,Tc]; rw [cc,Tc,l9c] at hx
      have ne' : i' ≠ j' := fun e => ne (by rw [e])
      rcases hx with rfl | hx
      · exact offCanon i' _ (cellOut j' i').1 (cellOut j' i').2
      · have inj : InTabF (T j') (K j') (SD j') (C j') (U j') (V j') (O j') (OP j') x := by
          rcases hx with h | h
          · exact Or.inl h
          · exact Or.inr h
        exact offCanon i' x (sep j' i' (Ne.symm ne') x (physFoot j' x inj)) (physLt j' x inj)
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [l9l,Tl]; exact (hOut x hx).2.2
    · rw [l9c,Tc]; exact offCanon j x ((hOut x hx).2.1 j) (hOut x hx).1
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [cl,Tl,l9l]; exact ⟨cellB,hdrB⟩
    · rw [cc,Tc,l9c]
      obtain ⟨inv,_,_⟩ := al j
      exact ⟨cells j,inv.cell0,inv.cell8,inv.cell16,inv.cell24,inv.cell32,inv.cell40,inv.cell48,inv.cell56,inv.cell64⟩
  · rw [Tc,l9c]
    obtain ⟨inv,oi,_⟩ := al ko
    exact ⟨F,s,rfl,rfl,rfl,inv.code,inv,oi⟩
  · rw [l9c] at hx; exact physLt ko x (Or.inr hx)

#print axioms regT_of_ready_snoc
set_option maxHeartbeats 16000000 in
/-- Registry establishment at the actual original `state_fresh_tx` call from the block table's layout facts only: if
the table at cell `bsC` has a valid canonical layout at the entry heap with its header in memory, arrays below the
entry heap and its cell off its footprint, the eight new transaction tables together with it form `RegT 9` at the exit
heap (content table among the transaction tables; outside words: below the entry heap and off the block table). This
is the form carried between transactions by the registry. -/
theorem stateFreshTx_regT9L {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (bsC TB : BitVec 64) (lB : TLay) (okB : lB.ok TB pointer) (hdrB : lB.hdr state.memory TB)
    (cellB : state.memory bsC = .word TB) (cBoff : ¬ lB.canon TB pointer bsC)
    (arrB : ∀ x, lB.arr x → x.toNat < pointer.toNat) :
    ∃ widths post H, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      TransactionRuntimeWorld widths (allocationEnd pointer 72) pointer journal snapshot 0 post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word H)) ∧ pointer.toNat ≤ H.toNat ∧
      (∀ ko : Fin 8, RegT 9 (c9 pointer (allocationEnd pointer 72) bsC) (T9 (allocationEnd pointer 72) TB)
        (fun x => x.toNat < pointer.toNat ∧ ¬ lB.canon TB pointer x) H post.memory post.memaddrs post.be
        ko.castSucc) ∧
      state.clock ≤ post.clock + 338 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals := by
  obtain ⟨widths,post,run,world,cost,remaining,locals,_⟩ := evaluate_stateFreshTx_transaction_runtime_world state
    base pointer oldTs bs journal snapshot oldCount code heap tsGlobal bsGlobal journalGlobal counterGlobal reservation
    journalBefore domain (by omega) journalAligned capacityGlobal
  obtain ⟨post',run',memKeep,_,ma,mb,mc,_⟩ := stateFreshTx_call_tables state pointer oldTs bs oldCount code heap tsGlobal
    bsGlobal counterGlobal reservation domain ticks
  have same : post' = post := congrArg Prod.snd (run'.symm.trans run)
  subst same
  obtain ⟨_,_,budget⟩ := stateFreshTx_reservation pointer reservation
  set p := allocationEnd pointer 72 with hp
  -- the exit heap pointer
  have reg : ∀ j, txTab p j ∈ stateFreshTxRegistryAfter p stateFreshTxAllTables ∅ := fun j =>
    stateFreshTx_binding_registered stateFreshTxAllTables p ∅ (txIdx p j) (txIdx_mem p j)
  obtain ⟨H,K0,SD0,C0,U0,V0,O0,OP0,N0,b0,rd0,_⟩ := world.journalWorld.world.ready _ (reg 0)
  have fr0 := rd0.live.frontier
  have hH : post'.globals.lookup (ofString "heap_ptr") = some (.val (.word H)) := fr0.heap
  have a0 := rd0.live.arrays
  have hdr0 := world.tableHeaders _ (reg 0)
  have := fr0.allocated; have := a0.headerKeys; have := a0.keysBefore; have := a0.usedBefore; have := a0.orderBefore
  have pH : pointer.toNat ≤ H.toNat := by omega
  -- the transaction tables at exit lie in [pointer + 72, H)
  have tsB := world.tsBound
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
  have tsFootLt : ∀ j x, rollbackTableFootprint widths (txTab p j) post' x → x.toNat < H.toNat := by
    rintro j x ⟨P',K',SD',C',U',V',O',OP',N',b',rd',ph⟩
    have e : P' = H := by
      have h1 : post'.globals.lookup (ofString "heap_ptr") = some (.val (.word P')) := rd'.live.frontier.heap
      rw [hH] at h1; simpa using h1.symm
    have := rd'.live.frontier.allocated; rw [e] at this
    have a' := rd'.live.arrays
    have := a'.headerKeys; have := a'.headerValues; have := a'.keysBefore; have := a'.valuesBefore
    have := a'.usedBefore; have := a'.orderBefore
    rcases ph with h | h | h | h | h | h <;> omega
  have tabLt : ∀ j, (txTab p j).toNat < H.toNat := by
    intro j
    obtain ⟨P',K',SD',C',U',V',O',OP',N',b',rd'⟩ := TabReady.of_rollback
      ((world.journalWorld.world.ready _ (reg j)).after_read (after := post') rfl rfl rfl rfl rfl)
    exact tsFootLt j _ ⟨P',K',SD',C',U',V',O',OP',N',b',rd',Or.inl ⟨le_refl _,by omega⟩⟩
  -- the block table's layout at the exit heap
  have hdrP := okB.hdrP
  have cBlt : bsC.toNat < pointer.toNat := by
    by_contra h; exact cBoff (Or.inr (Or.inr (by omega)))
  have okH : lB.ok TB H := hlay_canon okB pH
  have fitB : TB.toNat + 72 < 2 ^ 64 := by have := okB.eEnd; omega
  have hdrH : lB.hdr post'.memory TB := hdr_keep hdrB fitB (fun x lo hi => memKeep x (by omega))
  have canonLo : ∀ x, lB.canon TB H x → lB.canon TB pointer x := fun x h => canon_mono h pH
  have extraLt : ∀ x, (x = bsC ∨ HdrR TB x ∨ lB.arr x) → x.toNat < pointer.toNat := by
    rintro x (rfl | ⟨_,h⟩ | h)
    · exact cBlt
    · omega
    · exact arrB x h
  refine ⟨widths,post',H,run,world,hH,pH,fun ko => ?_,cost,remaining,locals⟩
  have e9 := regT_of_ready_snoc post' widths (txCell pointer p) (txTab p) ko H hH
    (fun j => TabReady.of_rollback ((world.journalWorld.world.ready _ (reg j)).after_read rfl rfl rfl rfl rfl))
    (fun j => stateFreshTx_registry_aligned stateFreshTxAllTables p ∅ (allocationEnd_aligned pointer 72)
      (fun t h => False.elim h) _ (reg j))
    (fun i j ne x hx => world.journalWorld.separated _ (reg i) _ (reg j) (fun e => ne (txTab_inj p budget e)) x hx)
    (fun j => world.fields (txIdx p j) (txIdx_mem p j))
    (fun i j => ⟨fun hf => by
        have := above _ _ hf; have := world.tableHeaders _ (reg j); have := cellNat i; have := offs i; omega,
      by have := world.tableHeaders _ (reg i); have := cellNat i; have := offs i; have := tabLt i; omega⟩)
    bsC TB lB okH hdrH (by rw [memKeep bsC cBlt]; exact cellB) (fun h => cBoff (canonLo _ h))
    (fun x h => by have := arrB x h; omega)
    (fun x hx i hf => by have := extraLt x hx; have := tsFoot i x hf; omega)
    (fun i x hx hc => by
      have lo : pointer.toNat ≤ x.toNat := by
        rcases hx with rfl | hf
        · have := cellNat i; omega
        · have := tsFoot i x hf; omega
      have hi : x.toNat < H.toNat := by
        rcases hx with rfl | hf
        · have := world.tableHeaders _ (reg i); have := cellNat i; have := offs i; have := tabLt i; omega
        · exact tsFootLt i x hf
      rcases hc with ⟨_,h⟩ | h | h
      · omega
      · have := arrB x h; omega
      · omega)
    (fun x => x.toNat < pointer.toNat ∧ ¬ lB.canon TB pointer x)
    (fun x ⟨hlt,hnot⟩ => ⟨by omega,fun j hf => by have := tsFoot j x hf; omega,fun h => hnot (canonLo x h)⟩)
  have ec : (Fin.lastCases bsC (txCell pointer p) : Fin 9 → BitVec 64) = c9 pointer p bsC := rfl
  have eT : (Fin.lastCases TB (txTab p) : Fin 9 → BitVec 64) = T9 p TB := rfl
  rw [ec,eT] at e9
  exact e9

#print axioms stateFreshTx_regT9L
/-- Layout facts of any registry table, as needed by `stateFreshTx_regT9L` for the next transaction (all but the
arrays-below-heap fact, which the registry records only for its content table). -/
theorem regT_tab_facts {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    {D : BitVec 64 → Prop} {B : Bool} {ko : Fin n} (h : RegT n c T Out H M D B ko) (i : Fin n) :
    ∃ l : TLay, l.ok (T i) H ∧ l.hdr M (T i) ∧ M (c i) = .word (T i) ∧ ¬ l.canon (T i) H (c i) ∧
      (i = ko → ∀ x, l.arr x → x.toNat < H.toNat) := by
  obtain ⟨l,pure,mem,_,ab⟩ := h
  exact ⟨l i,(pure.1 i).1,(mem i).2,(mem i).1,(pure.1 i).2,fun e => by subst e; exact ab⟩

#print axioms regT_tab_facts
end InitECandidate.Runtime
