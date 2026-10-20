import InitECandidate.Runtime.PtUBLoop1GD
/-!
The storage item body of `update_builder_from_tx` (`ubStorThen`) in the builder world: the index-start value
(world-level `idx_start_storage`), the post-state value, `u256_eq` (read-only), and the storage write or its removal.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Names declared by the storage item. -/
def storNames : List MlS := [ofString "pre_v",ofString "post_v",ofString "eq2"]

section si
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko kB : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop}
  {Sk : BitVec 64 → Prop} {Nj : BitVec 64}
  {ADs0 : Set (BitVec 64)} {Rg0 : BalK → BitVec 64 → Prop} {H0 : BitVec 64} {Rr0 Ow0 : BitVec 64 → Prop} {M0 : Mem}

theorem ubStorThen_aqgd (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64)
    (pairs : List (MlS × BitVec 64)) (hpn : ∀ p ∈ pairs, p.1 ∉ storNames) (Iv : BitVec 64)
    (hidx : (ofString "idx",Iv) ∈ pairs) (b2 A V2 be Kk Pv : BitVec 64)
    (hA : A.toNat % 8 = 0) (hAE : A.toNat + 52 ≤ 33806089496)
    (hS : Kk.toNat % 8 = 0) (hSE : Kk.toNat + 52 ≤ 33806089496)
    (hwP : w.toNat < P0.toNat) (hw0 : w.toNat < H0.toNat) (hwk0 : ∀ k, BalK.live ADs0 k → ¬ Rg0 k w)
    (hwR0 : ¬ Rr0 w) (hwO0 : ¬ Ow0 w) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ((LK pairs L ∧ L.lookup (ofString "s2") =
        some (.rStruct [.val (.word b2),.val (.word A),.val (.word V2)])) ∧ L.lookup (ofString "e") =
        some (.rStruct [.val (.word be),.val (.word Kk),.val (.word Pv)])) ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G)
      (fun L M G => (LK pairs L ∧ L.lookup (ofString "s2") =
        some (.rStruct [.val (.word b2),.val (.word A),.val (.word V2)])) ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G)
      (fun _ _ _ => False) ubStorThen := by
  have hne : ∀ x ∈ storNames, ∀ p ∈ pairs, p.1 ≠ x := fun x hx p hp e => hpn p hp (e ▸ hx)
  have lkI : ∀ {L : GA}, LK pairs L → L.lookup (ofString "idx") = some (.val (.word Iv)) := fun h => lk_get h _ _ hidx
  let LS : GA → Prop := fun L => (LK pairs L ∧ L.lookup (ofString "s2") =
    some (.rStruct [.val (.word b2),.val (.word A),.val (.word V2)])) ∧ L.lookup (ofString "e") =
    some (.rStruct [.val (.word be),.val (.word Kk),.val (.word Pv)])
  have ls_upd : ∀ (x : MlS), x ∈ storNames → ofString "s2" ≠ x → ofString "e" ≠ x → ∀ L v, LS L →
      LS (L.update (x,v)) := fun x hx h1 h2 L v ⟨⟨lk,l1⟩,l2⟩ =>
    ⟨⟨lk_update lk _ _ (hne x hx),by rw [lookup_update_ne' _ _ h1]; exact l1⟩,by rw [lookup_update_ne' _ _ h2]; exact l2⟩
  unfold ubStorThen
  let LS2 : GA → Prop := fun L => LK pairs L ∧ L.lookup (ofString "s2") =
    some (.rStruct [.val (.word b2),.val (.word A),.val (.word V2)])
  refine aqgd_conseq (aqgd_ust (LP' := LS2) (X := fun _ => False)
    (fun A2 R2 H2 Rr2 Ow2 M2 G2 u2 le2 hk2 hr2 ho2 => ?_) hw0 hwk0 hwR0 hwO0)
    (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim)
  have hw2 : w.toNat < H2.toNat := by omega
  let W2 := fun M G => USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj A2 R2 H2 Rr2 Ow2 M2 M G
  let Q2 : GA → Mem → GA → Prop := fun L M G => LS2 L ∧ W2 M G
  have rq2 : ∀ (x : MlS), x ∈ storNames → ofString "s2" ≠ x → ∀ (L : GA) (M : Mem) (G : GA) (L' : GA) (M' : Mem)
      (G' : GA), Q2 L' M' G' → Q2 (L'.resVarEq (x,L.lookup x)) M' G' := fun x hx hs _ _ _ _ _ _ ⟨⟨lk,l2⟩,st⟩ =>
    ⟨⟨lk_resVar lk _ _ (hne x hx),by rw [resVar_lookup_ne _ _ _ _ hs]; exact l2⟩,st⟩
  -- pre_v = idx_start_storage(s2.1, e.1)
  refine aqgd_decCall_issW bk wsr ne Bs hBs hcB (LP := LS)
    (Pc := fun L M G => LS L ∧ W2 M G) (Qc := Q2) (ofString "pre_v") _ _ A Kk u2 hwP hk2 hr2 ho2 ?_ ?_ ?_
    (fun L L' M' G' _ q => rq2 _ (by simp [storNames]) (by decide) L M2 G2 L' M' G' q)
  · intro F s _ _ _ ⟨⟨_,l1⟩,l2⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,l1,l2]
  · intro L a b c' d M G ls st
    exact ⟨ls_upd _ (by simp [storNames]) (by decide) (by decide) _ _ ls,st⟩
  -- post_v = lds {1,1,1,1} (e.2)
  refine aqgd_decD (Pb := fun L M G => ∃ q : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64, (LS L ∧
      L.lookup (ofString "post_v") = some (.rStruct [.val (.word q.1),.val (.word q.2.1),.val (.word q.2.2.1),
        .val (.word q.2.2.2)])) ∧ W2 M G) (Qb := Q2) _ _ _ (fun h => h.elim) ?_ ?_
    (fun L M G L' M' G' _ q => rq2 _ (by simp [storNames]) (by decide) L M G L' M' G' q)
  · intro F s v _ _ _ _ ⟨ls,hw⟩ _ ev _
    obtain ⟨a,b,c',d,rfl⟩ := ev_load4_words s _ v ev
    exact ⟨(a,b,c',d),⟨ls_upd _ (by simp [storNames]) (by decide) (by decide) _ _ ls,lookup_update_eq' _ _ _⟩,hw⟩
  refine aqgd_ex (fun q => ?_)
  rcases q with ⟨v0,v1,v2,v3⟩
  -- eq2 = u256_eq(pre_v, post_v): read-only
  let LV : GA → Prop := fun L => LS L ∧
    L.lookup (ofString "post_v") = some (.rStruct [.val (.word v0),.val (.word v1),.val (.word v2),.val (.word v3)])
  refine aqgd_decCall_mfF (I := fun L M G => LV L ∧ W2 M G) (I' := fun L M G => LV L ∧ W2 M G) (Q := Q2)
    _ _ _ _ _ _ _ vmLookup_u256_eq (memoryFrame_of_good vmLookup_u256_eq (by decide) (by decide))
    (by body_check Guest.guestFn_u256_eq) (by body_check Guest.guestFn_u256_eq)
    (fun L M G v ⟨⟨ls,lv⟩,hw⟩ => ⟨⟨ls_upd _ (by simp [storNames]) (by decide) (by decide) _ _ ls,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lv⟩,hw⟩) ?_
    (fun L M G L' M' G' _ q => rq2 _ (by simp [storNames]) (by decide) L M G L' M' G' q)
  -- the storage write or its removal
  refine aqgd_conseq (aqgd_ust (LP' := fun L => LV L) (X := fun _ => False)
    (fun A3 R3 H3 Rr3 Ow3 M3 G3 u3 le3 hk3 hr3 ho3 => ?_) hw2 hk2 hr2 ho2)
    (fun _ _ _ h => h) (fun L M G ⟨⟨⟨lk,_⟩,_⟩,st⟩ => ⟨lk,st⟩) (fun _ _ _ h => h.1.elim)
  refine uw_heapFact u3 (fun ⟨p3,_,_⟩ => ?_)
  refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
    (aqgd_conseq (aqgd_call_addStorageW bk wsr.1 _ _ _ _ A Kk Iv v0 v1 v2 v3 hA hAE hS hSE u3 hwP p3 hk3 Dall
      (fun s _ _ ⟨⟨⟨lk,l1⟩,l2⟩,lv⟩ => by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,l1,l2,lkI lk,lv]))
      (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    (aqgd_conseq (aqgd_call_removeStorageW bk wsr.1 _ _ _ A Kk Iv hA hAE hS hSE u3 hwP p3 hk3 Dall
      (fun s _ _ ⟨⟨⟨lk,l1⟩,l2⟩,_⟩ => by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,l1,l2,lkI lk]))
      (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))

#print axioms ubStorThen_aqgd
end si
end InitECandidate.Runtime
