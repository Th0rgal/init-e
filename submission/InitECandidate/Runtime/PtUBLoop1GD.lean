import InitECandidate.Runtime.PtUBItemGD
/-!
The accounts loop of `update_builder_from_tx` (`ubLoop1`) in the builder world: for each ordinal `i < count` of the
accounts-written table `aw` (content kept from the builder entry, its region outside every region the builder writes),
`htab_item` and, for a live item, the account item body.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section l1
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko kB : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop}
  {Sk : BitVec 64 → Prop} {Nj : BitVec 64}
  {ADs0 : Set (BitVec 64)} {Rg0 : BalK → BitVec 64 → Prop} {H0 : BitVec 64} {Rr0 Ow0 : BitVec 64 → Prop} {M0 : Mem}

/-- A source table outside every region the builder writes keeps its content along world steps from the entry. -/
theorem tcont_of_ust {Tt : BitVec 64} {l : TLay} {M : Mem} {G : GA} (tc0 : TCont D B M0 Tt l)
    (nc : l.N.toNat ≤ l.C.toNat)
    (hOut : ∀ x, InTabF Tt l.KS l.SD l.C l.US l.VS l.OS l.OPS x →
      x.toNat < H0.toNat ∧ (∀ k, BalK.live ADs0 k → ¬ Rg0 k x) ∧ ¬ Rr0 x ∧ ¬ Ow0 x)
    (st : USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G) : TCont D B M Tt l := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,fr⟩ := st
  exact tc0.frame nc (fun x hx => let ⟨a,b,c',d⟩ := hOut x hx; fr x a b c' d)

/-- One iteration of the accounts loop. -/
theorem ubIter1_aqgd (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) {k40 : Fin n} (ne40 : k40 ≠ ko) (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hc40 : c k40 = Ts + 40#64)
    (hSkSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSk : ∀ x, SkWin SKB x → Sk x)
    (Iv Taw : BitVec 64) (law : TLay) (tc0 : TCont D B M0 Taw law) (kl0 : 20 ≤ law.KL.toNat)
    (nc0 : law.N.toNat < law.C.toNat)
    (hAw : ∀ x, InTabF Taw law.KS law.SD law.C law.US law.VS law.OS law.OPS x →
      x.toNat < H0.toNat ∧ (∀ k, BalK.live ADs0 k → ¬ Rg0 k x) ∧ ¬ Rr0 x ∧ ¬ Ow0 x)
    (hwP : w.toNat < P0.toNat) (hw0 : w.toNat < H0.toNat) (hwk0 : ∀ k, BalK.live ADs0 k → ¬ Rg0 k w)
    (hwR0 : ¬ Rr0 w) (hwO0 : ¬ Ow0 w) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ((LK [(ofString "idx",Iv),(ofString "aw",Taw),(ofString "cap",law.N)] L ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G) ∧
        ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ law.N.toNat) ∧
        ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < law.N.toNat)
      (fun L M G => (LK [(ofString "idx",Iv),(ofString "aw",Taw),(ofString "cap",law.N)] L ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G) ∧
        ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ law.N.toNat)
      (fun _ _ _ => False)
      (.decCall (ofString "s") (.comb [.one,.one,.one]) (ofString "htab_item")
        [.var .local (ofString "aw"),.var .local (ofString "i")]
        ((ProgHOL.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0#64)) ubAcctThen .skip).seq
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64])))) := by
  let po : List (MlS × BitVec 64) := [(ofString "idx",Iv),(ofString "aw",Taw),(ofString "cap",law.N)]
  let W := fun M G => USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G
  refine aqgd_conseq (P := fun L M G => ∃ I : BitVec 64, (LK po L ∧ L.lookup (ofString "i") = some (.val (.word I))) ∧
      (W M G ∧ I.toNat < law.N.toNat))
    (aqgd_ex (fun I => ?_)) (fun L M G ⟨⟨⟨lk,st⟩,_⟩,I,hi,hlt⟩ => ⟨I,⟨lk,hi⟩,st,hlt⟩) (fun _ _ _ h => h)
    (fun _ _ _ h => h)
  refine aqgd_ghostR (fun M1 G1 ⟨st,hI⟩ => ?_)
  have tc := tcont_of_ust tc0 nc0.le hAw st
  have tc' := tc
  obtain ⟨_,s',_,_,_,_,inv,_⟩ := tc'
  have endB := inv.endBound
  have hC : 2 ≤ law.C.toNat := by omega
  have e1 : (I + 1).toNat = I.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  have hpo : ∀ p ∈ (ofString "i",I) :: po, p.1 ∉ itemNames := by
    intro p hp
    simp only [po,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  have pne : ∀ (x : MlS), x ≠ ofString "idx" → x ≠ ofString "aw" → x ≠ ofString "cap" → ∀ p ∈ po, p.1 ≠ x := by
    intro x h1 h2 h3 p hp
    simp only [po,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl
    exacts [h1.symm,h2.symm,h3.symm]
  refine aqgd_decCall_htabItem_tc
    (LP := fun L => LK po L ∧ L.lookup (ofString "i") = some (.val (.word I)))
    (Pc := fun L M G => (∃ q : BitVec 64 × BitVec 64 × BitVec 64, ((LK po L ∧
      L.lookup (ofString "i") = some (.val (.word I))) ∧ L.lookup (ofString "s") =
        some (.rStruct [.val (.word q.1),.val (.word q.2.1),.val (.word q.2.2)])) ∧
      q.2.1.toNat % 8 = 0 ∧ q.2.1.toNat + 52 ≤ 33806089496) ∧ W M G)
    (Qc := fun L M G => (LK po L ∧ W M G) ∧ ∃ I' : BitVec 64, L.lookup (ofString "i") = some (.val (.word I')) ∧
      I'.toNat ≤ law.N.toNat)
    (ofString "s") (.var .local (ofString "aw")) (.var .local (ofString "i")) Taw I law M1 G1 tc hI nc0 ?_
    (fun h => h.elim) ?_ ?_ ?_
  · intro F s _ _ _ ⟨lk,hi⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,lk_get lk (ofString "aw") Taw (by simp [po]),hi]
  · intro L b slot vv ⟨lk,hi⟩ sl _ _
    obtain ⟨k8,k52⟩ := item_key_ok inv kl0 hC sl
    exact ⟨⟨(b,_,vv),⟨⟨lk_update lk _ _ (pne _ (by decide) (by decide) (by decide)),
      by rw [lookup_update_ne' _ _ (by decide)]; exact hi⟩,lookup_update_eq' _ _ _⟩,k8,k52⟩,st⟩
  · refine aqgd_seq (Q := fun L M G => (LK ((ofString "i",I) :: po) L) ∧ W M G)
      (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
        (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
        (aqgd_conseq aqgd_skip (fun L M G ⟨⟨⟨q,⟨⟨lk,hi⟩,_⟩,_⟩,st⟩,_⟩ => ⟨fun p hp => by
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hi
          · exact lk p hp,st⟩) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
    · refine aqgd_conseq (P := fun L M G => ∃ q : BitVec 64 × BitVec 64 × BitVec 64,
          ((LK ((ofString "i",I) :: po) L ∧ L.lookup (ofString "s") =
            some (.rStruct [.val (.word q.1),.val (.word q.2.1),.val (.word q.2.2)])) ∧ W M G) ∧
          (q.2.1.toNat % 8 = 0 ∧ q.2.1.toNat + 52 ≤ 33806089496))
        (aqgd_ex (fun q => aqgd_pureE (fun ⟨k8,k52⟩ => ?_)))
        (fun L M G ⟨⟨⟨q,⟨⟨lk,hi⟩,ls⟩,kk⟩,st⟩,_⟩ => ⟨q,⟨⟨fun p hp => by
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hi
          · exact lk p hp,ls⟩,st⟩,kk⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
      rcases q with ⟨b,K,P⟩
      exact ubAcctThen_aqgd bk wsr ne Bs hBs hcB ne40 Ts hTs hc40 hSkSO hSk ((ofString "i",I) :: po) hpo Iv
        (by simp [po]) b K P k8 k52 hwP hw0 hwk0 hwR0 hwO0 Dall
    · refine aqgd_assignLocal _ _ (fun s v _ _ ⟨lk,st⟩ _ ev => ?_)
      have hi : s.locals.lookup (ofString "i") = some (.val (.word I)) := lk_get lk _ _ (by simp)
      simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
      subst ev
      exact ⟨⟨fun p hp => by
        rw [lookup_update_ne' _ _ (pne _ (by decide) (by decide) (by decide) p hp)]
        exact lk p (List.mem_cons_of_mem _ hp),st⟩,I + 1,lookup_update_eq' _ _ _,by rw [e1]; omega⟩
  · intro L L' M' G' _ ⟨⟨lk,st⟩,I',hi,hle⟩
    exact ⟨⟨lk_resVar lk _ _ (pne _ (by decide) (by decide) (by decide)),st⟩,I',
      by rw [resVar_lookup_ne _ _ _ _ (by decide)]; exact hi,hle⟩

#print axioms ubIter1_aqgd
/-- The accounts loop. -/
theorem ubLoop1_aqgd (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) {k40 : Fin n} (ne40 : k40 ≠ ko) (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hc40 : c k40 = Ts + 40#64)
    (hSkSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSk : ∀ x, SkWin SKB x → Sk x)
    (Iv Taw : BitVec 64) (law : TLay) (tc0 : TCont D B M0 Taw law) (kl0 : 20 ≤ law.KL.toNat)
    (nc0 : law.N.toNat < law.C.toNat)
    (hAw : ∀ x, InTabF Taw law.KS law.SD law.C law.US law.VS law.OS law.OPS x →
      x.toNat < H0.toNat ∧ (∀ k, BalK.live ADs0 k → ¬ Rg0 k x) ∧ ¬ Rr0 x ∧ ¬ Ow0 x)
    (hwP : w.toNat < P0.toNat) (hw0 : w.toNat < H0.toNat) (hwk0 : ∀ k, BalK.live ADs0 k → ¬ Rg0 k w)
    (hwR0 : ¬ Rr0 w) (hwO0 : ¬ Ow0 w) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LK [(ofString "idx",Iv),(ofString "aw",Taw),(ofString "cap",law.N)] L ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G) ∧
        ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ law.N.toNat)
      (fun L M G => (LK [(ofString "idx",Iv),(ofString "aw",Taw),(ofString "cap",law.N)] L ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G) ∧
        ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ law.N.toNat)
      (fun _ _ _ => False) ubLoop1 := by
  have tc0' := tc0
  obtain ⟨_,_,_,_,_,_,inv0,_⟩ := tc0'
  have endB := inv0.endBound
  unfold ubLoop1
  refine aqgd_conseq (aqgd_whileE (C := fun L _ _ => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧
      I.toNat < law.N.toNat) (E := fun _ _ _ => True) (Qb := fun _ _ _ => False) _ ?_
      (fun _ _ _ _ _ _ _ _ => trivial)
      (aqgb_of_aqgd (ubIter1_aqgd bk wsr ne Bs hBs hcB ne40 Ts hTs hc40 hSkSO hSk Iv Taw law tc0 kl0 nc0 hAw hwP hw0
        hwk0 hwR0 hwO0 Dall)))
    (fun _ _ _ h => h) (fun _ _ _ h => h.elim (fun h => h.1) False.elim) (fun _ _ _ h => h)
  intro F s x _ _ ⟨⟨lk,_⟩,I,hi,hle⟩ _ ev hx
  have hcap : s.locals.lookup (ofString "cap") = some (.val (.word law.N)) := lk_get lk _ _ (by simp)
  simp [EV,evalHOLExact,hi,hcap,slt_small (b := law.N) (show I.toNat < 2 ^ 63 by omega)] at ev
  split at ev
  · rename_i h; exact ⟨I,hi,h.2⟩
  · exact absurd ev.symm hx

#print axioms ubLoop1_aqgd
end l1
end InitECandidate.Runtime
