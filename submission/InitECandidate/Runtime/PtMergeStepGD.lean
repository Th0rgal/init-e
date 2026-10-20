import InitECandidate.Runtime.PtMergeLoopGD
import InitECandidate.Runtime.PtNewTabGD
/-!
Call steps of the `merge_tx_into_block` storage loop: `name = htab_new(KL, Cp)` assigned to a local (fresh valid table
at or above the heap pointer at the call, memory below it kept, journal counter kept).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ns
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `name = htab_new(KL, Cp)` (assigning call) from heap pointer `H`. -/
theorem aqgd_callAssign_htabNew {LP : GA → Prop} (name : MlS) (KL Cp H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (hH1 : HeapIs G1 H) (hN1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hw : w.toNat < H.toNat) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => ∃ (L0 : GA) (Tt H' : BitVec 64), L = L0.update (name,.val (.word Tt)) ∧ LP L0 ∧
        H.toNat ≤ Tt.toNat ∧ (∀ x, x.toNat < H.toNat → M x = M1 x) ∧ HeapIs G H' ∧ Tt.toNat + 72 ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496 ∧ NewTab Tt H' KL Cp M ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      RR (.call (some (some (.local,name),none)) (ofString "htab_new") [.const KL,.const Cp]) := by
  refine aqgd_callAssignF (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      LK [(ofString "cap",Cp),(ofString "key_len",KL)] L ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (∃ Tt : BitVec 64, v = .val (.word Tt) ∧ H.toNat ≤ Tt.toNat ∧
        (∀ x, x.toNat < H.toNat → M' x = M0' x) ∧ OnlyHeap G0' G' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
          Tt.toNat + 72 ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧ NewTab Tt H' KL Cp M') ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    _ _ _ _ _ _ originalRuntimeCode_htabNew_lookup (by simp) (fun h => h) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G0') (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact aw.2) ?_
    intro hsc
    have h1 := aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_htabNew_lookup
      (by decide)) (htabNew_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
        (SKB := SKB) (Nj := Nj) (w := w) KL Cp H hw M0' G0'))
      (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_htabNew_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_htabNew_lookup (by decide)) h1) ?_ (fun _ _ _ h => h.elim) ?_
    · intro L M G ⟨lk,hM',hG'⟩
      rw [hM',hG']
      exact ⟨⟨⟨⟨lk,rfl,by rw [hG]; exact hH1⟩,rfl⟩,hsc⟩,by rw [hG]; exact hN1⟩
    · intro v M' G' ⟨⟨rr,_⟩,hn'⟩
      exact ⟨rr,hn'⟩
  · intro F s values callee rs _ H' hG _ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact] at ev1 ev2; subst ev1 ev2
    have e := callee_eq originalRuntimeCode_htabNew_lookup lookup
    refine ⟨fun p hp => ?_,rfl,rfl⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨lp,hM,_⟩ ⟨⟨Tt,ev,hHT,fr,_,H',hH',hT,hE,nt⟩,hn'⟩
    subst ev
    exact ⟨L,Tt,H',rfl,lp,hHT,fun x hx => by rw [fr x hx,hM],hH',hT,hE,nt,hn'⟩

#print axioms aqgd_callAssign_htabNew
end ns

/-- Storage-loop locals: `outer`, `bouter`, `cap`, the counter `i = I`, the item `s`. -/
def MLs (O BO N I : BitVec 64) (sv : ValueHOL 64) (L : GA) : Prop :=
  L.lookup (ofString "outer") = some (.val (.word O)) ∧ L.lookup (ofString "bouter") = some (.val (.word BO)) ∧
  L.lookup (ofString "cap") = some (.val (.word N)) ∧ L.lookup (ofString "i") = some (.val (.word I)) ∧
  L.lookup (ofString "s") = some sv

theorem mls_upd {O BO N I : BitVec 64} {sv : ValueHOL 64} {L : GA} (h : MLs O BO N I sv L) (x : MlS)
    (v : ValueHOL 64) (h1 : ofString "outer" ≠ x) (h2 : ofString "bouter" ≠ x) (h3 : ofString "cap" ≠ x)
    (h4 : ofString "i" ≠ x) (h5 : ofString "s" ≠ x) : MLs O BO N I sv (L.update (x,v)) := by
  obtain ⟨a,b,c,hi,d⟩ := h
  exact ⟨by rw [lookup_update_ne' _ _ h1]; exact a,by rw [lookup_update_ne' _ _ h2]; exact b,
    by rw [lookup_update_ne' _ _ h3]; exact c,by rw [lookup_update_ne' _ _ h4]; exact hi,
    by rw [lookup_update_ne' _ _ h5]; exact d⟩

theorem mls_res {O BO N I : BitVec 64} {sv : ValueHOL 64} {L : GA} (h : MLs O BO N I sv L) (x : MlS)
    (o : Option (ValueHOL 64)) (h1 : ofString "outer" ≠ x) (h2 : ofString "bouter" ≠ x) (h3 : ofString "cap" ≠ x)
    (h4 : ofString "i" ≠ x) (h5 : ofString "s" ≠ x) : MLs O BO N I sv (L.resVarEq (x,o)) := by
  obtain ⟨a,b,c,hi,d⟩ := h
  exact ⟨by rw [resVar_lookup_ne _ _ _ _ h1]; exact a,by rw [resVar_lookup_ne _ _ _ _ h2]; exact b,
    by rw [resVar_lookup_ne _ _ _ _ h3]; exact c,by rw [resVar_lookup_ne _ _ _ _ h4]; exact hi,
    by rw [resVar_lookup_ne _ _ _ _ h5]; exact d⟩

section gh
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- Fix the current memory and globals as ghosts. -/
theorem aqgd_ghostR {LP : GA → Prop} {P : Mem → GA → Prop} {Q : GA → Mem → GA → Prop} {p : ProgHOL 64}
    (h : ∀ M1 G1, P M1 G1 → AQGD D B A w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR p) :
    AQGD D B A w Vn (fun L M G => LP L ∧ P M G) Q RR p :=
  fun F s code dom aw sl H hH ⟨lp,pm⟩ => h s.memory H pm F s code dom aw sl H hH ⟨lp,rfl,rfl⟩
end gh

section mi
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- One merged item `s = (b, K, vv)` of the storage loop (`mergeInner`): `m = htab_get(bouter, s.1)`; a fresh inner
table set into `bouter` when absent, else the present inner table; then `htab_union_into(binner, s.2)`. -/
theorem mergeInner_aqgd (BO : BitVec 64) (lb0 : TLay) (R0 : Set (BitVec 64)) (Os0 : BitVec 64 → BitVec 64 → Prop)
    (H0 Nj : BitVec 64) (M0 : Mem) (O N I b K vv : BitVec 64) (R : Set (BitVec 64))
    (hwB : ¬ TabPhys BO lb0 w) (hwO : ∀ t ∈ R0, ¬ Os0 t w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H0.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) (hK : K.toNat % 8 = 0)
    (hKE : K.toNat + 52 ≤ 33806089496) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧
        MLR D B BO lb0 R0 Os0 H0 Nj M0 R M G)
      (fun L M G => MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧
        ∃ R' : Set (BitVec 64), MLR D B BO lb0 R0 Os0 H0 Nj M0 R' M G) RR mergeInner := by
  unfold mergeInner
  refine aqgd_ghostR (fun M1 G1 ⟨H,Hl,lb,Os,mw⟩ => ?_)
  have mw' := mw
  obtain ⟨⟨hH1,h01,hn1⟩,⟨rv,hHl,kl,sd⟩,_,_,_,_⟩ := mw'
  obtain ⟨wB,_,wH⟩ := mlw_out mw hwB hwO (by omega)
  refine aqgd_decCall_htabGet_rv (LP := MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]))
    (Pc := fun L M G => (MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧
      ∃ p val : BitVec 64, L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧
        (p ≠ 0 → val ∈ R)) ∧ M = M1 ∧ G = G1)
    (Qc := fun L M G => MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧
      ∃ R' : Set (BitVec 64), MLR D B BO lb0 R0 Os0 H0 Nj M0 R' M G)
    (ofString "m") _ _ BO K Hl H lb R M1 G1 rv hH1 hHl Dall (Or.inl kl) hK hKE ?_ (fun h => h.elim) ?_ ?_ ?_
  · intro F s _ _ _ lp
    obtain ⟨_,hbo,_,_,hs⟩ := lp
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,hbo,hs]
  · intro L p val lp _ prop
    exact ⟨⟨mls_upd lp _ _ (by decide) (by decide) (by decide) (by decide) (by decide),p,val,
      lookup_update_eq' _ _ _,prop⟩,rfl,rfl⟩
  · refine aqgd_dec (Pb := fun L M G => (MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧
        ∃ p val : BitVec 64, L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧
          (p ≠ 0 → val ∈ R)) ∧ M = M1 ∧ G = G1)
      (Qb := fun L M G => MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧ ∃ R' : Set (BitVec 64), MLR D B BO lb0 R0 Os0 H0 Nj M0 R' M G)
      (ofString "binner") .one (.const 0) (fun h => h.elim) ?_ ?_ ?_
    · intro F s v H' _ _ ⟨⟨lp,p,val,hm,prop⟩,hM,hG⟩ _ _ _
      exact ⟨⟨mls_upd lp _ _ (by decide) (by decide) (by decide) (by decide) (by decide),p,val,
        by rw [lookup_update_ne' _ _ (by decide)]; exact hm,prop⟩,hM,hG⟩
    · refine aqgd_seq (Q := fun L M G => MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧ ∃ (Bn : BitVec 64) (R' : Set (BitVec 64)),
        L.lookup (ofString "binner") = some (.val (.word Bn)) ∧ Bn ∈ R' ∧ MLR D B BO lb0 R0 Os0 H0 Nj M0 R' M G)
        ?_ ?_
      · -- mergeChoose
        unfold mergeChoose
        refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun L _ _ => ∃ p val : BitVec 64,
            L.lookup (ofString "m") = some (.rStruct [.val (.word p),.val (.word val)]) ∧ p ≠ 0) _ ?_ ?_ ?_
        · intro F s x H' _ _ ⟨⟨_,p,val,hm,_⟩,_,_⟩ _ ev
          refine ⟨fun _ => trivial,fun hx => ⟨p,val,hm,fun hp => ?_⟩⟩
          subst hp hx
          simp [EV,evalHOLExact,hm,Compiler.Encoders.Asm.wordCmpHOL] at ev
        · -- binner = htab_new(32, 8); htab_set(bouter, s.1, binner)
          unfold mergeNewSet
          refine aqgd_seq (aqgd_conseq (aqgd_callAssign_htabNew (LP := MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)])) (ofString "binner") 32#64 8#64
              H Nj M1 G1 hH1 hn1 wH) (fun L M G ⟨⟨⟨lp,_⟩,hM,hG⟩,_⟩ => ⟨lp,hM,hG⟩)
            (Q' := fun L M G => ∃ q : BitVec 64 × BitVec 64 × (BitVec 64 → BitVec 64 → Prop),
              (MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧ L.lookup (ofString "binner") = some (.val (.word q.1))) ∧
              MLW D B BO lb0 R0 Os0 H0 Nj M0 (insert q.1 R) q.2.1 Hl lb q.2.2 M G) ?_ (fun _ _ _ h => h)) ?_
          · intro L M G ⟨L0,Tt,H',eL,lp,hHT,fr,hH',hT,hE,nt,hn'⟩
            subst eL
            have tv : TabV Tt Tt H' M := tabV_ofNew (b := 3) nt hT hE (le_refl _) (by decide) (by decide) (by decide)
              (by decide) (by decide)
            obtain ⟨_,mw2⟩ := mlw_new (M' := M) mw hHT hH' hT hn' (fun x hx => fr x hx) tv
            exact ⟨(Tt,H',_),⟨mls_upd lp _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
              lookup_update_eq' _ _ _⟩,mw2⟩
          · refine aqgd_ex (fun q => ?_)
            rcases q with ⟨Tt,H',Os'⟩
            refine aqgd_ghostR (LP := fun L => MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧ L.lookup (ofString "binner") = some (.val (.word Tt)))
              (P := MLW D B BO lb0 R0 Os0 H0 Nj M0 (insert Tt R) H' Hl lb Os') (fun M2 G2 mw2 => ?_)
            have mw2' := mw2
            obtain ⟨⟨hH2,_,hn2⟩,⟨rv2,hHl2,_,_⟩,_,_,_,_⟩ := mw2'
            obtain ⟨wB2,_,_⟩ := mlw_out mw2 hwB hwO (by omega)
            refine aqgd_conseq (aqgd_call_htabSet_rv2 (LP := fun L => MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧
                L.lookup (ofString "binner") = some (.val (.word Tt)))
              (.var .local (ofString "bouter")) (.rfield 1 (.var .local (ofString "s"))) (.var .local (ofString "binner"))
              BO K Tt Hl H' Nj lb (insert Tt R) M2 G2 hwP wB2 rv2 hH2 hn2 hHl2 Dall (Or.inl kl) sd
              (Set.mem_insert _ _) hK hKE ?_) (fun _ _ _ h => h) ?_ (fun _ _ _ h => h)
            · intro F s _ _ _ ⟨lp,hb⟩
              obtain ⟨_,hbo,_,_,hs⟩ := lp
              rw [evalListHOLFinite_eq_toExact]
              simp [evalListHOLExact,evalHOLExact,hbo,hs,hb]
            · intro L M G ⟨⟨⟨lp,hb⟩,Hp,hHp,le,hn',fr⟩,srv⟩
              exact ⟨lp,Tt,insert Tt R,hb,Set.mem_insert _ _,mlw_set mw2 fr hn' srv⟩
        · -- binner = m.1
          refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨lp,p,val,hm,prop⟩,hM,hG⟩,⟨p',val',hm',hp'⟩⟩ _ ev => ?_)
          rw [hm] at hm'
          simp only [Option.some.injEq,ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,
            HolWordLab.word.injEq,and_true] at hm'
          obtain ⟨rfl,rfl⟩ := hm'
          simp [EV,evalHOLExact,hm] at ev
          subst ev
          exact ⟨mls_upd lp _ _ (by decide) (by decide) (by decide) (by decide) (by decide),val,R,
            lookup_update_eq' _ _ _,prop hp',H,Hl,lb,Os,by rw [hM,hG]; exact mw⟩
      · -- htab_union_into(binner, s.2)
        unfold mergeUnionInner
        refine aqgd_conseq (P := fun L M G => ∃ q : BitVec 64 × Set (BitVec 64),
            (MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧ L.lookup (ofString "binner") = some (.val (.word q.1))) ∧
            (q.1 ∈ q.2 ∧ MLR D B BO lb0 R0 Os0 H0 Nj M0 q.2 M G))
          (aqgd_ex (fun q => ?_)) (fun L M G ⟨lp,Bn,R',hb,hm,mr⟩ => ⟨(Bn,R'),⟨lp,hb⟩,hm,mr⟩) (fun _ _ _ h => h)
          (fun _ _ _ h => h)
        rcases q with ⟨Bn,R'⟩
        refine aqgd_ghostR (fun M2 G2 ⟨hBn,H2,Hl2,lb2,Os2,mw2⟩ => ?_)
        have mw2' := mw2
        obtain ⟨⟨hH2,h02,hn2⟩,_,f2,_,_,_⟩ := mw2'
        obtain ⟨_,wO2,_⟩ := mlw_out mw2 hwB hwO (by omega)
        refine aqgd_conseq (aqgd_call_unionO (LP := fun L => MLs O BO N I (.rStruct [.val (.word b),.val (.word K),.val (.word vv)]) L ∧
            L.lookup (ofString "binner") = some (.val (.word Bn)))
          (.var .local (ofString "binner")) (.rfield 2 (.var .local (ofString "s"))) (Os2 Bn) Bn H2 Nj M2 G2
          (f2.1 Bn hBn) hH2 hn2 (wO2 Bn hBn) hwP (by omega) ?_) (fun _ _ _ h => h) ?_ (fun _ _ _ h => h)
        · intro F s _ _ _ ⟨lp,hb⟩
          obtain ⟨_,_,_,_,hs⟩ := lp
          refine ⟨vv,?_⟩
          rw [evalListHOLFinite_eq_toExact]
          simp [evalListHOLExact,evalHOLExact,hs,hb]
        · intro L M G ⟨⟨lp,_⟩,u⟩
          exact ⟨lp,R',mlw_union hBn mw2 u⟩
    · intro L M G L' M' G' _ ⟨lp,R',mr⟩
      exact ⟨mls_res lp _ _ (by decide) (by decide) (by decide) (by decide) (by decide),R',mr⟩
  · intro L L' M' G' _ ⟨lp',R',mr⟩
    exact ⟨mls_res lp' _ _ (by decide) (by decide) (by decide) (by decide) (by decide),R',mr⟩

#print axioms mergeInner_aqgd
end mi
end InitECandidate.Runtime
