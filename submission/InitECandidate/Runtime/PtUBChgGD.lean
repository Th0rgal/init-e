import InitECandidate.Runtime.PtUBAcctGD
/-!
The change decisions of the account item of `update_builder_from_tx` (`ubChgRest`): `u256_eq` (read-only), the
balance change or its removal, the nonce change or its removal, `memeq` on the code hashes (read-only) and the code
change (through the world-level `get_code`) or its removal; all world steps from the entry world.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ch
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop}
  {Sk : BitVec 64 → Prop} {Nj : BitVec 64}
  {ADs0 : Set (BitVec 64)} {Rg0 : BalK → BitVec 64 → Prop} {H0 : BitVec 64} {Rr0 Ow0 : BitVec 64 → Prop} {M0 : Mem}

/-- Names written by the change decisions. -/
def chgNames : List MlS :=
  [ofString "post_bal",ofString "post_nonce",ofString "post_ch",ofString "eq",ofString "code"]

theorem ubChgRest_aqgd (bk : BalKeep) (wsf : WsIFrame WsI) {k40 : Fin n} (ne40 : k40 ≠ ko) (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hc40 : c k40 = Ts + 40#64)
    (hSkSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSk : ∀ x, SkWin SKB x → Sk x)
    (pairs : List (MlS × BitVec 64)) (hpn : ∀ p ∈ pairs, p.1 ∉ chgNames) (Iv K : BitVec 64)
    (hidx : (ofString "idx",Iv) ∈ pairs) (haddr : (ofString "addr",K) ∈ pairs)
    (hK : K.toNat % 8 = 0) (hKE : K.toNat + 52 ≤ 33806089496)
    (hwP : w.toNat < P0.toNat) (hw0 : w.toNat < H0.toNat) (hwk0 : ∀ k, BalK.live ADs0 k → ¬ Rg0 k w)
    (hwR0 : ¬ Rr0 w) (hwO0 : ¬ Ow0 w) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LK pairs L ∧ PVL L) ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G)
      (fun L M G => LK pairs L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G)
      (fun _ _ _ => False) ubChgRest := by
  have hne : ∀ x ∈ chgNames, ∀ p ∈ pairs, p.1 ≠ x := fun x hx p hp e => hpn p hp (e ▸ hx)
  have lkI : ∀ {L : GA}, LK pairs L → L.lookup (ofString "idx") = some (.val (.word Iv)) := fun h => lk_get h _ _ hidx
  have lkA : ∀ {L : GA}, LK pairs L → L.lookup (ofString "addr") = some (.val (.word K)) := fun h => lk_get h _ _ haddr
  let W := fun M G => USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G
  have pvl_eq : ∀ L v, PVL L → PVL (L.update (ofString "eq",v)) := fun L v ⟨⟨a,b,c',d,h1⟩,⟨y,h2⟩,⟨z,h3⟩⟩ =>
    ⟨⟨a,b,c',d,by rw [lookup_update_ne' _ _ (by decide)]; exact h1⟩,⟨y,by rw [lookup_update_ne' _ _ (by decide)]; exact h2⟩,
      ⟨z,by rw [lookup_update_ne' _ _ (by decide)]; exact h3⟩⟩
  unfold ubChgRest
  -- eq = u256_eq(pre_bal, post_bal): read-only
  refine aqgd_decCall_mfF (I := fun L M G => (LK pairs L ∧ PVL L) ∧ W M G)
    (I' := fun L M G => (LK pairs L ∧ PVL L) ∧ W M G) (Q := fun L M G => LK pairs L ∧ W M G)
    _ _ _ _ _ _ _ vmLookup_u256_eq (memoryFrame_of_good vmLookup_u256_eq (by decide) (by decide))
    (by body_check Guest.guestFn_u256_eq) (by body_check Guest.guestFn_u256_eq)
    (fun L M G v ⟨⟨lk,pv⟩,hw⟩ => ⟨⟨lk_update lk _ _ (hne _ (by simp [chgNames])),pvl_eq L v pv⟩,hw⟩) ?_
    (fun L M G L' M' G' _ ⟨lk,hw⟩ => ⟨lk_resVar lk _ _ (hne _ (by simp [chgNames])),hw⟩)
  -- the balance decision
  refine aqgd_seq (Q := fun L M G => (LK pairs L ∧ PVL L) ∧ W M G) ?_ ?_
  · refine aqgd_conseq (P := fun L M G => ∃ q : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64,
        ((LK pairs L ∧ PVL L) ∧ L.lookup (ofString "post_bal") = some (.rStruct [.val (.word q.1),
          .val (.word q.2.1),.val (.word q.2.2.1),.val (.word q.2.2.2)])) ∧ W M G)
      (aqgd_ex (fun q => ?_)) (fun L M G ⟨⟨lk,pv⟩,hw⟩ => let ⟨a,b,c',d,h⟩ := pv.1; ⟨(a,b,c',d),⟨⟨lk,pv⟩,h⟩,hw⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    rcases q with ⟨b0,b1,b2,b3⟩
    refine aqgd_conseq (aqgd_ust (LP' := fun L => (LK pairs L ∧ PVL L) ∧
        L.lookup (ofString "post_bal") = some (.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),
          .val (.word b3)])) (X := fun _ => False)
      (fun A2 R2 H2 Rr2 Ow2 M2 G2 u2 le2 hk2 hr2 ho2 => ?_) hw0 hwk0 hwR0 hwO0)
      (fun _ _ _ h => h) (fun L M G ⟨⟨lp,_⟩,st⟩ => ⟨lp,st⟩) (fun _ _ _ h => h.1.elim)
    refine uw_heapFact u2 (fun ⟨p2,_,_⟩ => ?_)
    refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_conseq (aqgd_call_addBalanceW bk wsf _ _ _ K Iv b0 b1 b2 b3 hK hKE u2 hwP p2 hk2 Dall
        (fun s _ _ ⟨⟨lk,_⟩,lb⟩ => by
          rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,lkA lk,lkI lk,lb]))
        (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
      (aqgd_conseq (aqgd_call_removeChangeW bk wsf _ _ _ _ K 16#64 40#64 Iv (Or.inl ⟨rfl,rfl⟩) hK hKE u2 hwP p2 hk2
        Dall (fun s _ _ ⟨⟨lk,_⟩,_⟩ => by
          rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,lkA lk,lkI lk]))
        (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
  -- the nonce decision
  refine aqgd_seq (Q := fun L M G => (LK pairs L ∧ PVL L) ∧ W M G) ?_ ?_
  · refine aqgd_conseq (P := fun L M G => ∃ y : BitVec 64,
        ((LK pairs L ∧ PVL L) ∧ L.lookup (ofString "post_nonce") = some (.val (.word y))) ∧ W M G)
      (aqgd_ex (fun y => ?_)) (fun L M G ⟨⟨lk,pv⟩,hw⟩ => let ⟨y,h⟩ := pv.2.1; ⟨y,⟨⟨lk,pv⟩,h⟩,hw⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_ust (LP' := fun L => (LK pairs L ∧ PVL L) ∧
        L.lookup (ofString "post_nonce") = some (.val (.word y))) (X := fun _ => False)
      (fun A2 R2 H2 Rr2 Ow2 M2 G2 u2 le2 hk2 hr2 ho2 => ?_) hw0 hwk0 hwR0 hwO0)
      (fun _ _ _ h => h) (fun L M G ⟨⟨lp,_⟩,st⟩ => ⟨lp,st⟩) (fun _ _ _ h => h.1.elim)
    refine uw_heapFact u2 (fun ⟨p2,_,_⟩ => ?_)
    refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_conseq (aqgd_call_addNonceW bk wsf _ _ _ K Iv y hK hKE u2 hwP p2 hk2 Dall
        (fun s _ _ ⟨⟨lk,_⟩,ln⟩ => by
          rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,lkA lk,lkI lk,ln]))
        (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
      (aqgd_conseq (aqgd_call_removeChangeW bk wsf _ _ _ _ K 24#64 16#64 Iv (Or.inr (Or.inl ⟨rfl,rfl⟩)) hK hKE u2
        hwP p2 hk2 Dall (fun s _ _ ⟨⟨lk,_⟩,_⟩ => by
          rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,lkA lk,lkI lk]))
        (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
  -- eq = memeq(pre_ch, post_ch, 32): read-only
  refine aqgd_seq (Q := fun L M G => (LK pairs L ∧ PVL L) ∧ W M G) (aqgd_callAssignF (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    _ _ _ _ _ _ originalRuntimeCode_memeq_lookup (by simp) (fun h => h)
    (fun _ M0' G0' _ => aqgd_of_mf (memoryFrame_of_good originalRuntimeCode_memeq_lookup (by decide) (by decide))
      (by body_check Guest.guestFn_memeq) (by body_check Guest.guestFn_memeq) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun L M G v M' G' ⟨⟨lk,pv⟩,hw⟩ ⟨e1,e2⟩ => by
      rw [e1,e2]; exact ⟨⟨lk_update lk _ _ (hne _ (by simp [chgNames])),pvl_eq L v pv⟩,hw⟩)) ?_
  -- the code decision
  refine aqgd_conseq (P := fun L M G => ∃ y : BitVec 64,
      ((LK pairs L ∧ PVL L) ∧ L.lookup (ofString "post_ch") = some (.val (.word y))) ∧ W M G)
    (aqgd_ex (fun y => ?_)) (fun L M G ⟨⟨lk,pv⟩,hw⟩ => let ⟨y,h⟩ := pv.2.2; ⟨y,⟨⟨lk,pv⟩,h⟩,hw⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_conseq (aqgd_ust (LP' := fun L => LK pairs L) (X := fun _ => False)
    (fun A2 R2 H2 Rr2 Ow2 M2 G2 u2 le2 hk2 hr2 ho2 => ?_) hw0 hwk0 hwR0 hwO0)
    (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim)
  refine uw_heapFact u2 (fun ⟨p2,_,_⟩ => ?_)
  refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
    (aqgd_conseq (aqgd_call_removeChangeW bk wsf _ _ _ _ K 32#64 24#64 Iv (Or.inr (Or.inr ⟨rfl,rfl⟩)) hK hKE u2
      hwP p2 hk2 Dall (fun s _ _ ⟨⟨lk,_⟩,_⟩ => by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,lkA lk,lkI lk]))
      (fun _ _ _ h => h.1) (fun L M G ⟨⟨⟨lk,_⟩,_⟩,st⟩ => ⟨lk,st⟩) (fun _ _ _ h => h))
  refine aqgd_conseq (aqgd_decCall_gcW bk wsf ne40 Ts hTs hc40 hSkSO hSk
    (LP := fun L => (LK pairs L ∧ PVL L) ∧ L.lookup (ofString "post_ch") = some (.val (.word y)))
    (Pc := fun L M G => ∃ q : BitVec 64 × BitVec 64, (LK pairs L ∧ L.lookup (ofString "code") =
      some (.rStruct [.val (.word q.1),.val (.word q.2)])) ∧
      USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj A2 R2 H2 Rr2 Ow2 M2 M G)
    (Qc := fun L M G => LK pairs L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj A2 R2 H2 Rr2 Ow2 M2 M G)
    (ofString "code") _ _ y K u2 hwP hk2 hr2 ho2 ?_ ?_ ?_ ?_)
    (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)
  · intro F s _ _ _ ⟨⟨lk,_⟩,lc⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,lkA lk,lc]
  · intro L a b M G ⟨⟨lk,_⟩,_⟩ st
    exact ⟨(a,b),⟨lk_update lk _ _ (hne _ (by simp [chgNames])),lookup_update_eq' _ _ _⟩,st⟩
  · refine aqgd_ex (fun q => ?_)
    rcases q with ⟨a,b⟩
    refine aqgd_conseq (aqgd_ust (LP' := fun L => LK pairs L ∧ L.lookup (ofString "code") =
        some (.rStruct [.val (.word a),.val (.word b)])) (X := fun _ => False)
      (fun A3 R3 H3 Rr3 Ow3 M3 G3 u3 le3 hk3 hr3 ho3 => ?_) (by omega) hk2 hr2 ho2)
      (fun _ _ _ h => h) (fun L M G ⟨⟨lk,_⟩,st⟩ => ⟨lk,st⟩) (fun _ _ _ h => h.1.elim)
    refine uw_heapFact u3 (fun ⟨p3,_,_⟩ => ?_)
    exact aqgd_conseq (aqgd_call_addCodeW bk wsf _ _ _ _ K Iv a b hK hKE u3 hwP p3 hk3 Dall
      (fun s _ _ ⟨lk,lc⟩ => by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,lkA lk,lkI lk,lc]))
      (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)
  · intro L L' M' G' _ ⟨lk,st⟩
    exact ⟨lk_resVar lk _ _ (hne _ (by simp [chgNames])),st⟩

#print axioms ubChgRest_aqgd
end ch
end InitECandidate.Runtime
