import InitECandidate.Runtime.PtNewTabGD
/-!
`process_transaction` spine drops 69-89: `m = msg_new()` with the heap fact `m + 176 ≤ heap`, the seven fenced
stores into `m`, `aa = htab_new(20, 64)` (above `m`), the `htab_set(aa, ..)` calls for `sender`, the 18 precompile
addresses and the `nal + 1` access-list addresses, `ak = htab_new(52, 16)` (above every `aa` array) and the
`htab_set(ak, ..)` loop over the keys; `SI` kept, `aa` stays valid below `ak`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section gs
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A store keeps the globals, so any globals property rides along. -/
theorem aqgd_store_glob {P Q : GA → Mem → GA → Prop} {X : GA → Prop} {d v : ExpHOL 64}
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s.locals s.memory s.globals →
      ∃ a : BitVec 64, EV s d = some (.val (.word a)))
    (h : AQGD D B A w Vn P Q RR (.store d v)) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ X G) (fun L M G => Q L M G ∧ X G) RR (.store d v) := by
  intro F s code dom aw sl G hG ⟨pre,x⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl G hG pre
  unfold GIs at hG; subst hG
  obtain ⟨ad,had⟩ := hd s pre
  obtain ⟨_,glob,_⟩ := evaluate_store_any s d v ad had
  refine ⟨m,a,fun e => ?_,r,c,b⟩
  obtain ⟨sl',G',hG',q⟩ := n e
  unfold GIs at hG'; subst hG'
  exact ⟨sl',_,rfl,q,by rw [glob]; exact x⟩

#print axioms aqgd_store_glob
end gs

section nbh
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Nj : BitVec 64} {M0 : Mem}

/-- `aqgd_decCall_newBlk_si` exposing the block `Hb` and `Hb + N ≤` heap pointer to the continuation. -/
theorem aqgd_decCall_newBlkH_si {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name fn x : MlS) (Nn : BitVec 64)
    {cont : ProgHOL 64} (installed : originalRuntimeCode.lookup fn = some ([],newBlkBody x Nn,.one))
    (smallN : Nn.toNat < 2 ^ 32) (hkBo : keepsG (ofString "bo") goodBo (newBlkBody x Nn) = true)
    (hkWs : keepsG (ofString "u256_ws") goodWs (newBlkBody x Nn) = true)
    (hkScr : keepsG (ofString "secp_accel_scratch") goodScr (newBlkBody x Nn) = true)
    (hw : w.toNat < Lo.toNat)
    (hup : ∀ L v, LP L → LP' (L.update (name,v)))
    (hcont : ∀ Hb : BitVec 64, Lo.toNat ≤ Hb.toNat → Hb.toNat + Nn.toNat ≤ 33806089496 →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => (LP' L ∧ L.lookup name = some (.val (.word Hb))) ∧ SI n c T Out ko D B Excl Lo Nj M0 M G ∧
          ∃ H : BitVec 64, HeapIs G H ∧ Hb.toNat + Nn.toNat ≤ H.toNat) Q RR cont)
    (hres : ∀ L M G L' M' G', LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) Q2 RR (.decCall name .one fn [] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ Hb : BitVec 64, HeapIs G0' Hb ∧ Hb.toNat % 8 = 0 ∧ Hb.toNat ≤ 33806089496 ∧
        (((v = .val (.word Hb) ∧ (∀ y, ¬ MWin Hb Nn.toNat y → M' y = M0' y) ∧
          ∃ H' : BitVec 64, HeapIs G' H' ∧ Hb.toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧
            OnlyHeap G0' G') ∧ ScrIs Sc G') ∧ G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := fun L M G => ∃ Hb : BitVec 64, ((LP' L ∧ L.lookup name = some (.val (.word Hb))) ∧
      SI n c T Out ko D B Excl Lo Nj M0 M G ∧ ∃ H : BitVec 64, HeapIs G H ∧ Hb.toNat + Nn.toNat ≤ H.toNat) ∧
        (Lo.toNat ≤ Hb.toNat ∧ Hb.toNat + Nn.toNat ≤ 33806089496)) (Qc := Q)
    _ _ _ _ _ _ _ installed (by simp) ?_ (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_
    (aqgd_exE (fun Hb => aqgd_pureE (fun ⟨a,b⟩ => hcont Hb a b))) hres
  · intro L0 M0' G0' ⟨_,⟨Hb,hH,hle⟩,_,hn,_⟩
    refine aqgd_of_arenaFact (Φ := (P0.toNat ≤ Hb.toNat ∧ Hb.toNat ≤ 33806089496 ∧ Hb.toNat % 8 = 0) ∧ ScrIs Sc G0')
      (fun _ _ g aw ⟨_,hg⟩ => by subst hg; exact ⟨jws_heap_facts aw.1.1.1 hH,aw.2⟩) ?_
    intro ⟨⟨_,hcapH,hal⟩,hsc⟩
    have hwb : ¬ MWin Hb Nn.toNat w := mwin_belowS hal (by omega) (by omega)
    have h1 := aqgd_conseq (aqgd_keepScr (Sc := Sc) hkScr (newBlk_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0)
      (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB) (Nj := Nj) x Nn Hb (by omega) hwb M0' G0'))
      (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo) hkBo hkWs h1) ?_ (fun _ _ _ h => h.elim) ?_
    · intro L M G ⟨hM,hG⟩
      subst hM hG
      exact ⟨⟨⟨⟨rfl,hH⟩,rfl⟩,hsc⟩,hn⟩
    · intro v M' G' ⟨⟨rr,sc⟩,hn'⟩
      exact ⟨Hb,hH,hal,hcapH,⟨rr,sc⟩,hn'⟩
  · intro L M G v M' G' ⟨lp,si⟩ ⟨Hb,hH,hal,hcap,⟨⟨⟨ev,fr,H',hH',c1,c2⟩,_⟩,_⟩,hn'⟩ _
    subst ev
    obtain ⟨H1,hH1,le1⟩ := si.1
    have e := heapIs_unique hH1 hH
    subst e
    exact ⟨H1,⟨⟨hup L _ lp,lookup_update_eq' _ _ _⟩,
      si_glob (si_mem si (fun y hy => fr y (mwin_belowS hal (by omega) (by omega)))) ⟨H',hH',by omega⟩ hn',
      H',hH',c1⟩,le1,by omega⟩

#print axioms aqgd_decCall_newBlkH_si

theorem msgNew_inst : originalRuntimeCode.lookup (ofString "msg_new") =
    some ([],newBlkBody (ofString "m") 176#64,.one) := by
  rw [← msgNew_eq]; exact originalRuntimeCode_msgNew_lookup

/-- Table `aa` valid in `[Taa, Pa)` with `Pa` at most the heap pointer and at most `Ub`. -/
def TBu (Taa Ub : BitVec 64) (M : Mem) (G : GA) : Prop :=
  ∃ Pa H : BitVec 64, TabV Taa Taa Pa M ∧ HeapIs G H ∧ Pa.toNat ≤ H.toNat ∧ Pa.toNat ≤ Ub.toNat

/-- A `htab_set` loop `while c { htab_set(tn, ek, 1); i = i + 1 }` keeping `SI`, `TBf Tt A` and `R`. -/
theorem aqgd_setLoop {LP : GA → Prop} {R : Mem → GA → Prop} (c0 : ExpHOL 64) (tn : MlS) (ek : ExpHOL 64)
    (Tt A : BitVec 64) (hLoA : Lo.toNat ≤ A.toNat) (hw : w.toNat < Lo.toNat)
    (ht : ∀ L, LP L → L.lookup tn = some (.val (.word Tt)))
    (hi : ∀ L v, LP L → LP (L.update (ofString "i",v)))
    (hR : ∀ (M M' : Mem) (G G' : GA) (P H H' : BitVec 64), R M G → HeapIs G H → HeapIs G' H' →
      H.toNat ≤ H'.toNat → (∀ x : BitVec 64, ¬ (A.toNat ≤ x.toNat ∧ x.toNat < P.toNat) → x.toNat < H.toNat →
        M' x = M x) → R M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ TBf Tt A M G ∧ R M G)
      (fun L M G => (LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ TBf Tt A M G ∧ R M G) RR
      (.while c0 (.seq (.call (some (none,none)) (ofString "htab_set") [.var .local tn,ek,.const 1])
        (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)])))) :=
  aqgd_whileI _ (aqgd_seq (aqgd_conseq (aqgd_call_htabSet_si tn ek (.const 1) Tt A hLoA hw ht hR)
      (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    (aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨lp,si⟩,tb,r⟩ _ _ => ⟨⟨hi _ v lp,si⟩,tb,r⟩)))

#print axioms aqgd_setLoop

/-- Spine drops 69-89 of the actual `process_transaction`. -/
theorem ptSegMsg {QM : Mem → GA → Prop} {DF : Nat} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62)
    (hw : w.toNat < Lo.toNat) (Ix S : BitVec 64) {cont : ProgHOL 64}
    (hcont : ∀ Mm Taa Tak : BitVec 64, Lo.toNat ≤ Mm.toNat → Mm.toNat + 176 ≤ Taa.toNat → Lo.toNat ≤ Taa.toNat →
      Lo.toNat ≤ Tak.toNat →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => ((((LTe Ix S Lo L ∧ L.lookup (ofString "m") = some (.val (.word Mm))) ∧
          L.lookup (ofString "aa") = some (.val (.word Taa))) ∧ L.lookup (ofString "ak") = some (.val (.word Tak))) ∧
          SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ TBu Taa Tak M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) (fun _ M G => QM M G) RR
      (.decCall (ofString "m") .one (ofString "msg_new") []
        (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 0)]) (.var .global (ofString "be")))
        (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 8)]) (.var .local (ofString "te")))
        (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 16)]) (.var .local (ofString "sender")))
        (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 24)]) (.load .one (.op .add [(.var .local (ofString "tx")),(.const 152)])))
        (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 40)]) (.var .local (ofString "mgas")))
        (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 48)]) (.var .local (ofString "reservoir")))
        (.seq (.store (.op .add [(.var .local (ofString "m")),(.const 56)]) (.load (.comb [.one,.one,.one,.one]) (.op .add [(.var .local (ofString "tx")),(.const 160)])))
        (.decCall (ofString "aa") .one (ofString "htab_new") [(.const 20),(.const 64)]
        (.seq .skip
        (.seq (.call (some (none,none)) (ofString "htab_set") [(.var .local (ofString "aa")),(.var .local (ofString "sender")),(.const 1)])
        (.seq .skip
        (.seq (.assign .local (ofString "i") (.const 0))
        (.seq (.while (.cmp .less (.var .local (ofString "i")) (.const 18)) (.seq (.call (some (none,none)) (ofString "htab_set") [(.var .local (ofString "aa")),(.op .add [(.var .global (ofString "precompile_addrs")),(.panop .mul [(.var .local (ofString "i")),(.const 20)])]),(.const 1)]) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)]))))
        (.seq (.assign .local (ofString "i") (.const 0))
        (.seq (.while (.cmp .less (.var .local (ofString "i")) (.op .add [(.var .local (ofString "nal")),(.const 1)])) (.seq (.call (some (none,none)) (ofString "htab_set") [(.var .local (ofString "aa")),(.load .one (.op .add [(.var .local (ofString "al_addrs")),(.panop .mul [(.var .local (ofString "i")),(.const 8)])])),(.const 1)]) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)]))))
        (.seq .skip
        (.decCall (ofString "ak") .one (ofString "htab_new") [(.const 52),(.const 16)]
        (.seq (.assign .local (ofString "i") (.const 0))
        (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nkeys"))) (.seq (.call (some (none,none)) (ofString "htab_set") [(.var .local (ofString "ak")),(.op .add [(.var .local (ofString "al_keys")),(.panop .mul [(.var .local (ofString "i")),(.const 52)])]),(.const 1)]) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)]))))
        (.seq .skip
        cont))))))))))))))))))))) := by
  have hD : DF + 8 ≤ 2 ^ 64 := by omega
  refine aqgd_decCall_newBlkH_si (LP' := LTe Ix S Lo) _ _ _ 176#64 msgNew_inst (by decide)
    (keepsBo_of_installed msgNew_inst (by decide)) (keepsWs_of_installed msgNew_inst (by decide))
    (keepsScr_of_installed msgNew_inst (by decide)) hw
    (fun L v lp => lte_upd lp _ v (by decide) (by decide) (by decide)) (fun Mm leM fitM => ?_)
    (fun _ _ _ _ _ _ _ h => h)
  let LM := fun L : GA => LTe Ix S Lo L ∧ L.lookup (ofString "m") = some (.val (.word Mm))
  let X := fun G : GA => ∃ H : BitVec 64, HeapIs G H ∧ Mm.toNat + (176#64).toNat ≤ H.toNat
  refine aqgd_conseq (P := fun L M G => (LM L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ X G) ?_
    (fun _ _ _ ⟨a,b,x⟩ => ⟨⟨a,b⟩,x⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  have hfb : ∀ L, LM L → FB (ofString "m") Lo 176 L := fun L h => ⟨Mm,h.2,leM,by simpa using fitM⟩
  have st := fun (k : BitVec 64) (hk : k.toNat < 176) (v : ExpHOL 64) =>
    aqgd_store_glob (X := X) (fun s h => ⟨Mm + k,ev_addc s _ Mm k h.1.2⟩)
      (aqgd_stFB_si (D := D) (B := B) (A := JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) (w := w) (Vn := fun _ => False)
        (RR := RR) (n := n) (c := c) (T := T) (Out := Out) (ko := ko) (Excl := Excl) (Nj := Nj) (M0 := M0)
        (LP := LM) hF hD hw (ofString "m") 176 k hk hfb v)
  refine aqgd_seq (st 0#64 (by decide) _) ?_
  refine aqgd_seq (st 8#64 (by decide) _) ?_
  refine aqgd_seq (st 16#64 (by decide) _) ?_
  refine aqgd_seq (st 24#64 (by decide) _) ?_
  refine aqgd_seq (st 40#64 (by decide) _) ?_
  refine aqgd_seq (st 48#64 (by decide) _) ?_
  refine aqgd_seq (st 56#64 (by decide) _) ?_
  -- aa = htab_new(20, 64)
  refine aqgd_decCall_htabNew_si (LP' := LM) (R0 := fun _ G => X G) (R1 := fun Tt _ _ => Mm.toNat + 176 ≤ Tt.toNat)
    _ 20#64 64#64 6 (by decide) (by decide) (by decide) (by decide) (by decide) hw ?_
    (fun L v lp => ⟨lte_upd lp.1 _ v (by decide) (by decide) (by decide),
      by rw [lookup_update_ne' _ _ (by decide)]; exact lp.2⟩) (fun Taa leA => ?_) (fun _ _ _ _ _ _ _ h => h)
  · intro M M' G G' H H' Tt ⟨H0,hH0,le0⟩ hH hHT _ _ _
    have := heapIs_unique hH0 hH; subst this
    have : (176#64).toNat = 176 := rfl
    omega
  let LA := fun L : GA => LM L ∧ L.lookup (ofString "aa") = some (.val (.word Taa))
  refine aqgd_conseq (P := fun L M G => ((LA L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ TBf Taa Taa M G) ∧
    Mm.toNat + 176 ≤ Taa.toNat) ?_ (fun _ _ _ ⟨⟨a,b⟩,c,d⟩ => ⟨⟨⟨a,b⟩,c⟩,d⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_pureE (fun hMA => ?_)
  refine aqgd_conseq (P := fun L M G => (LA L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ TBf Taa Taa M G ∧ True) ?_
    (fun _ _ _ ⟨a,b⟩ => ⟨a,b,trivial⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  have laI : ∀ L v, LA L → LA (L.update (ofString "i",v)) := fun L v h =>
    ⟨⟨lte_upd h.1.1 _ v (by decide) (by decide) (by decide),by rw [lookup_update_ne' _ _ (by decide)]; exact h.1.2⟩,
      by rw [lookup_update_ne' _ _ (by decide)]; exact h.2⟩
  have trueR : ∀ (M M' : Mem) (G G' : GA) (P H H' : BitVec 64), True → HeapIs G H → HeapIs G' H' →
      H.toNat ≤ H'.toNat → (∀ x : BitVec 64, ¬ (Taa.toNat ≤ x.toNat ∧ x.toNat < P.toNat) → x.toNat < H.toNat →
        M' x = M x) → True := fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  refine aqgd_seq aqgd_skip ?_
  refine aqgd_seq (aqgd_call_htabSet_si (LP := LA) (R := fun _ _ => True) _ _ _ Taa Taa leA hw (fun L h => h.2) trueR) ?_
  refine aqgd_seq aqgd_skip ?_
  refine aqgd_seq (aqgd_assignLocal (Q := fun L M G => (LA L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧
    TBf Taa Taa M G ∧ True) _ _ (fun s v _ _ ⟨⟨lp,si⟩,tb,r⟩ _ _ => ⟨⟨laI _ v lp,si⟩,tb,r⟩)) ?_
  refine aqgd_seq (aqgd_setLoop _ _ _ Taa Taa leA hw (fun L h => h.2) laI trueR) ?_
  refine aqgd_seq (aqgd_assignLocal (Q := fun L M G => (LA L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧
    TBf Taa Taa M G ∧ True) _ _ (fun s v _ _ ⟨⟨lp,si⟩,tb,r⟩ _ _ => ⟨⟨laI _ v lp,si⟩,tb,r⟩)) ?_
  refine aqgd_seq (aqgd_setLoop _ _ _ Taa Taa leA hw (fun L h => h.2) laI trueR) ?_
  refine aqgd_seq aqgd_skip ?_
  -- ak = htab_new(52, 16)
  refine aqgd_conseq (P := fun L M G => (LA L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ TBf Taa Taa M G) ?_
    (fun _ _ _ ⟨a,b,_⟩ => ⟨a,b⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_decCall_htabNew_si (LP' := LA) (R0 := TBf Taa Taa) (R1 := fun Tt M G => TBu Taa Tt M G)
    _ 52#64 16#64 4 (by decide) (by decide) (by decide) (by decide) (by decide) hw ?_
    (fun L v lp => ⟨⟨lte_upd lp.1.1 _ v (by decide) (by decide) (by decide),
      by rw [lookup_update_ne' _ _ (by decide)]; exact lp.1.2⟩,by rw [lookup_update_ne' _ _ (by decide)]; exact lp.2⟩)
    (fun Tak leK => ?_) (fun _ _ _ _ _ _ _ h => h)
  · intro M M' G G' H H' Tt ⟨Pa,H0,tv,hH0,le0⟩ hH hHT hH' hT fr
    have := heapIs_unique hH0 hH; subst this
    exact ⟨Pa,H',tabV_frame tv (fun x _ hx => fr x (by omega)),hH',by omega,by omega⟩
  let LK2 := fun L : GA => LA L ∧ L.lookup (ofString "ak") = some (.val (.word Tak))
  have lkI : ∀ L v, LK2 L → LK2 (L.update (ofString "i",v)) := fun L v h =>
    ⟨laI L v h.1,by rw [lookup_update_ne' _ _ (by decide)]; exact h.2⟩
  have tbuR : ∀ (M M' : Mem) (G G' : GA) (P H H' : BitVec 64), TBu Taa Tak M G → HeapIs G H → HeapIs G' H' →
      H.toNat ≤ H'.toNat → (∀ x : BitVec 64, ¬ (Tak.toNat ≤ x.toNat ∧ x.toNat < P.toNat) → x.toNat < H.toNat →
        M' x = M x) → TBu Taa Tak M' G' := by
    intro M M' G G' P H H' ⟨Pa,H0,tv,hH0,le0,le1⟩ hH hH' le fr
    have := heapIs_unique hH0 hH; subst this
    exact ⟨Pa,H',tabV_frame tv (fun x _ hx => fr x (by omega) (by omega)),hH',by omega,le1⟩
  refine aqgd_seq (aqgd_assignLocal (Q := fun L M G => (LK2 L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧
    TBf Tak Tak M G ∧ TBu Taa Tak M G) _ _ (fun s v _ _ ⟨⟨lp,si⟩,tb,r⟩ _ _ => ⟨⟨lkI _ v lp,si⟩,tb,r⟩)) ?_
  refine aqgd_seq (aqgd_setLoop _ _ _ Tak Tak leK hw (fun L h => h.2) lkI tbuR) ?_
  refine aqgd_seq aqgd_skip ?_
  exact aqgd_conseq (hcont Mm Taa Tak leM hMA leA leK) (fun _ _ _ ⟨a,_,b⟩ => ⟨a,b⟩) (fun _ _ _ h => h)
    (fun _ _ _ h => h)

#print axioms ptSegMsg
end nbh
end InitECandidate.Runtime
