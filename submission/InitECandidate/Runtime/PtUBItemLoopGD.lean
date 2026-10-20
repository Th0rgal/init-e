import InitECandidate.Runtime.PtUBStorGD
/-!
A generic ordinal loop over a content table in the builder world:
`while ctr < cap { item = htab_item(tbl, ctr); if item.0 != 0 { body }; ctr = ctr + 1 }`, from a body spec for every
live item (ordinal `J < N`, aligned key, the order/value cells of the item at the iteration memory).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The loop program. -/
def itemLoopP (ctr capN tblN itemN : MlS) (body : ProgHOL 64) : ProgHOL 64 :=
  .while (.cmp .less (.var .local ctr) (.var .local capN))
    (.decCall itemN (.comb [.one,.one,.one]) (ofString "htab_item") [.var .local tblN,.var .local ctr]
      ((ProgHOL.ite (.cmp .notEqual (.rfield 0 (.var .local itemN)) (.const 0#64)) body .skip).seq
        (.assign .local ctr (.op .add [.var .local ctr,.const 1#64]))))

section il
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

theorem itemLoop_aqgd (ctr capN tblN itemN : MlS) (body : ProgHOL 64) (pairs : List (MlS × BitVec 64))
    (X : GA → Prop) (W : Mem → GA → Prop) (Tt : BitVec 64) (l : TLay)
    (hTC : ∀ M G, W M G → TCont D B M Tt l) (kl0 : 20 ≤ l.KL.toNat) (nc0 : l.N.toNat < l.C.toNat)
    (hcap : (capN,l.N) ∈ pairs) (htbl : (tblN,Tt) ∈ pairs)
    (hctr : ∀ p ∈ pairs, p.1 ≠ ctr) (hitem : ∀ p ∈ pairs, p.1 ≠ itemN) (hci : ctr ≠ itemN)
    (hXu : ∀ L v, X L → X (L.update (itemN,v)) ∧ X (L.update (ctr,v)))
    (hXr : ∀ L o, X L → X (L.resVarEq (itemN,o)))
    (hbody : ∀ (I b K P slot : BitVec 64), I.toNat < l.N.toNat → K.toNat % 8 = 0 → K.toNat + 52 ≤ 33806089496 →
      slot.toNat < l.C.toNat →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => (((LK ((ctr,I) :: pairs) L ∧ X L) ∧ L.lookup itemN =
          some (.rStruct [.val (.word b),.val (.word K),.val (.word P)])) ∧ W M G) ∧
          (M (l.OS + I * 8) = .word slot ∧ M (l.VS + slot * 8) = .word P))
        (fun L M G => (LK ((ctr,I) :: pairs) L ∧ X L) ∧ W M G) (fun _ _ _ => False) body) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ((LK pairs L ∧ X L) ∧ W M G) ∧
        ∃ I : BitVec 64, L.lookup ctr = some (.val (.word I)) ∧ I.toNat ≤ l.N.toNat)
      (fun L M G => ((LK pairs L ∧ X L) ∧ W M G) ∧
        ∃ I : BitVec 64, L.lookup ctr = some (.val (.word I)) ∧ I.toNat ≤ l.N.toNat)
      (fun _ _ _ => False) (itemLoopP ctr capN tblN itemN body) := by
  have endB : l.C.toNat * 8 < 2 ^ 63 ∨ True := Or.inr trivial
  unfold itemLoopP
  refine aqgd_conseq (aqgd_whileE (C := fun L _ _ => ∃ I : BitVec 64, L.lookup ctr = some (.val (.word I)) ∧
      I.toNat < l.N.toNat) (E := fun _ _ _ => True) (Qb := fun _ _ _ => False) _ ?_
      (fun _ _ _ _ _ _ _ _ => trivial) (aqgb_of_aqgd ?_))
    (fun _ _ _ h => h) (fun _ _ _ h => h.elim (fun h => h.1) False.elim) (fun _ _ _ h => h)
  · intro F s x _ _ ⟨⟨⟨lk,_⟩,hw⟩,I,hi,hle⟩ _ ev hx
    have tc := hTC _ _ hw
    obtain ⟨_,_,_,_,_,_,inv,_⟩ := tc
    have eB := inv.endBound
    have hc : s.locals.lookup capN = some (.val (.word l.N)) := lk_get lk _ _ hcap
    simp [EV,evalHOLExact,hi,hc,slt_small (b := l.N) (show I.toNat < 2 ^ 63 by omega)] at ev
    split at ev
    · rename_i h; exact ⟨I,hi,h.2⟩
    · exact absurd ev.symm hx
  refine aqgd_conseq (P := fun L M G => ∃ I : BitVec 64, ((LK pairs L ∧ X L) ∧ L.lookup ctr = some (.val (.word I))) ∧
      (W M G ∧ I.toNat < l.N.toNat))
    (aqgd_ex (fun I => ?_)) (fun L M G ⟨⟨⟨lx,hw⟩,_⟩,I,hi,hlt⟩ => ⟨I,⟨lx,hi⟩,hw,hlt⟩) (fun _ _ _ h => h)
    (fun _ _ _ h => h)
  refine aqgd_ghostR (fun M1 G1 ⟨hw,hI⟩ => ?_)
  have tc := hTC _ _ hw
  have tc' := tc
  obtain ⟨_,_,_,_,_,_,inv,_⟩ := tc'
  have eB := inv.endBound
  have hC : 2 ≤ l.C.toNat := by omega
  have e1 : (I + 1).toNat = I.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  refine aqgd_decCall_htabItem_tc
    (LP := fun L => (LK pairs L ∧ X L) ∧ L.lookup ctr = some (.val (.word I)))
    (Pc := fun L M G => (∃ q : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64, ((((LK ((ctr,I) :: pairs) L ∧ X L) ∧
      L.lookup itemN = some (.rStruct [.val (.word q.1),.val (.word q.2.1),.val (.word q.2.2.1)])) ∧ W M G) ∧
      (M (l.OS + I * 8) = .word q.2.2.2 ∧ M (l.VS + q.2.2.2 * 8) = .word q.2.2.1)) ∧
      (q.2.1.toNat % 8 = 0 ∧ q.2.1.toNat + 52 ≤ 33806089496 ∧ q.2.2.2.toNat < l.C.toNat)))
    (Qc := fun L M G => ((LK pairs L ∧ X L) ∧ W M G) ∧ ∃ I' : BitVec 64, L.lookup ctr = some (.val (.word I')) ∧
      I'.toNat ≤ l.N.toNat)
    itemN (.var .local tblN) (.var .local ctr) Tt I l M1 G1 tc hI nc0 ?_ (fun h => h.elim) ?_ ?_ ?_
  · intro F s _ _ _ ⟨⟨lk,_⟩,hi⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,lk_get lk _ _ htbl,hi]
  · intro L b slot vv ⟨⟨lk,lx⟩,hi⟩ sl cO cV
    obtain ⟨k8,k52⟩ := item_key_ok inv kl0 hC sl
    refine ⟨(b,_,vv,slot),⟨⟨⟨⟨fun p hp => ?_,(hXu L _ lx).1⟩,lookup_update_eq' _ _ _⟩,hw⟩,cO,cV⟩,k8,k52,sl⟩
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · rw [lookup_update_ne' _ _ hci]; exact hi
    · rw [lookup_update_ne' _ _ (hitem p hp)]; exact lk p hp
  · refine aqgd_seq (Q := fun L M G => (LK ((ctr,I) :: pairs) L ∧ X L) ∧ W M G)
      (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
        (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
        (aqgd_conseq aqgd_skip (fun L M G ⟨⟨q,⟨⟨⟨lx,_⟩,hw'⟩,_⟩,_⟩,_⟩ => ⟨lx,hw'⟩) (fun _ _ _ h => h)
          (fun _ _ _ h => h))) ?_
    · refine aqgd_conseq (P := fun L M G => ∃ q : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64,
          ((((LK ((ctr,I) :: pairs) L ∧ X L) ∧ L.lookup itemN = some (.rStruct [.val (.word q.1),.val (.word q.2.1),
            .val (.word q.2.2.1)])) ∧ W M G) ∧
          (M (l.OS + I * 8) = .word q.2.2.2 ∧ M (l.VS + q.2.2.2 * 8) = .word q.2.2.1)) ∧
          (q.2.1.toNat % 8 = 0 ∧ q.2.1.toNat + 52 ≤ 33806089496 ∧ q.2.2.2.toNat < l.C.toNat))
        (aqgd_ex (fun q => aqgd_pureE (fun ⟨k8,k52,sl⟩ => ?_))) (fun L M G ⟨h,_⟩ => h) (fun _ _ _ h => h)
        (fun _ _ _ h => h)
      rcases q with ⟨b,K,P,slot⟩
      exact hbody I b K P slot hI k8 k52 sl
    · refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨lk,lx⟩,hw'⟩ _ ev => ?_)
      have hi : s.locals.lookup ctr = some (.val (.word I)) := lk_get lk _ _ (by simp)
      simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
      subst ev
      exact ⟨⟨⟨fun p hp => by
        rw [lookup_update_ne' _ _ (hctr p hp)]
        exact lk p (List.mem_cons_of_mem _ hp),(hXu _ _ lx).2⟩,hw'⟩,I + 1,lookup_update_eq' _ _ _,by rw [e1]; omega⟩
  · intro L L' M' G' _ ⟨⟨⟨lk,lx⟩,hw'⟩,I',hi,hle⟩
    exact ⟨⟨⟨lk_resVar lk _ _ hitem,hXr _ _ lx⟩,hw'⟩,I',by rw [resVar_lookup_ne _ _ _ _ hci]; exact hi,hle⟩

#print axioms itemLoop_aqgd
end il
end InitECandidate.Runtime
