import InitECandidate.Runtime.PtSufBOGD
import InitECandidate.Runtime.PtSufAO2GD
/-!
`ptSufBO` over the arena with the `bal_*` globals pinned (`JWB`): the same actual statements; the receipt encoder call
re-derived over `JWB` (its installed body passes the `bal_*` keep check), the other leaves lifted.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem keepsAll_of_installed (bk : BalKeep2) {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64}
    {rs : ShapeHOL} (h : originalRuntimeCode.lookup f = some (params,body,rs)) (hf : goodBal2 f = true) :
    balWatched.all (fun g => keepsG g goodBal2 body) = true :=
  List.all_eq_true.mpr (fun g hg => keepsBal2_of_installed bk h hf g hg)

theorem goodBal2_encodeReceipt : goodBal2 (ofString "encode_receipt") = true := goodBal2_of_suf (by decide)
theorem goodBal2_lstNew : goodBal2 (ofString "lst_new") = true := goodBal2_of_extra (by decide)

section cs2
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc H0 : BitVec 64} {M0 : Mem} {Y : BitVec 64}
  {BA IA IS KB Ixb : BitVec 64}

/-- `rc = encode_receipt(e1, e2, e3, e4)` keeping `PXR`: the result is a two-word value. -/
theorem aqgd_decCall_encReceipt_pxrB {LP LP' : GA → Prop} (bk : BalKeep2) {Q Q2 : GA → Mem → GA → Prop} (name : MlS)
    (e1 e2 e3 e4 : ExpHOL 64) {cont : ProgHOL 64}
    (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x) (hOut : Out w)
    (hup : ∀ L v, LP L → U2V v → LP' (L.update (name,v)))
    (hcont : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => LP' L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q RR cont)
    (hres : ∀ L M G L' M' G', LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q2 RR
      (.decCall name (.comb [.one,.one]) (ofString "encode_receipt") [e1,e2,e3,e4] cont) := by
  have hwK : ¬ KPW K Pd w := by
    rintro (h | h)
    · exact (hOutSafe w hOut).1.2.1 h
    · exact (hOutSafe w hOut).1.2.2.1 h
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (((ERP L ∧ RG (hpOf G0') Sc G) ∧ M = M0') ∧
        G.lookup (ofString "journal_n") = some (.val (.word (wordOf G0' (ofString "journal_n"))))) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ((RG (hpOf G0') Sc G' ∧ ∀ x, x.toNat < (hpOf G0').toNat → ¬ KPW K Pd x → M' x = M0' x) ∧ ScrIs Sc G') ∧
        G'.lookup (ofString "journal_n") = some (.val (.word (wordOf G0' (ofString "journal_n")))))
    (Pc := fun L M G => LP' L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (Qc := Q)
    _ _ _ _ _ _ _ originalRuntimeCode_encodeReceipt_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hcont hres
  · intro L0 M0' G0' ⟨_,H,Nj,hH,_,reg,hn,_⟩
    rw [hpOf_eq hH,wordOf_eq hn]
    have hwH := regT_out_lt reg hOut
    refine aqgd_of_arenaFact (Φ := H.toNat % 8 = 0) (fun _ _ g aw ⟨_,hg⟩ => by
      subst hg; exact (jws_heap_facts aw.1.1.1.1 hH).2.2) ?_
    intro hal
    exact aqgd_liftB bk (keepsAll_of_installed bk originalRuntimeCode_encodeReceipt_lookup goodBal2_encodeReceipt) <|
      aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo) (Nj := Nj)
      (RR := fun _ M' G' => RG H Sc G' ∧ ∀ x, x.toNat < H.toNat → ¬ KPW K Pd x → M' x = M0' x)
      (keepsBo_of_installed originalRuntimeCode_encodeReceipt_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_encodeReceipt_lookup (by decide))
      (aqgd_conseq (erF (w := w) (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
        (SKB := SKB) (Nj := Nj) hF hDF hcap H Sc K Pd hK0 hPd0 hal hwH hwK M0') (fun _ _ _ h => h)
        (fun _ _ _ h => h) (fun _ _ _ h => ⟨h,h.1.2⟩)))
      (fun _ _ _ ⟨a,_⟩ => a) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs aw H' hG ⟨_,H,Nj,hH,_,_,hn,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,_,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,_,r3⟩ := evalList_cons' s _ _ _ r2
    obtain ⟨v4,vs4,rfl,_,r4⟩ := evalList_cons' s _ _ _ r3
    have := evalList_nil' s _ r4; subst this
    obtain ⟨a,b,cc,d,rfl,rfl,rfl,rfl⟩ := entry4_words originalRuntimeCode_encodeReceipt_lookup lookup
    have e := callee_eq originalRuntimeCode_encodeReceipt_lookup lookup
    refine ⟨⟨⟨⟨⟨⟨a,by rw [e]; simp (config := {decide := true})⟩,⟨b,by rw [e]; simp (config := {decide := true})⟩,
      ⟨cc,by rw [e]; simp (config := {decide := true})⟩,⟨d,by rw [e]; simp (config := {decide := true})⟩⟩,
      ⟨H,hH,by rw [hpOf_eq hH]⟩,aw.1.2⟩,rfl⟩,by rw [wordOf_eq hn]; exact hn⟩,rfl⟩
  · intro L M G v M' G' ⟨lp,H,Nj,hH,h0,reg,hn,fr⟩ ⟨⟨⟨⟨⟨H',hH',le⟩,_⟩,fk⟩,_⟩,hn'⟩ ok
    rw [hpOf_eq hH] at le fk
    rw [wordOf_eq hn] at hn'
    refine ⟨hup L v lp (u2v_of_check ok),H',Nj,hH',by omega,regT_mono (regT_keep_except reg (KPW K Pd) fk ?_ ?_) le,
      hn',fun x ho hx => ?_⟩
    · intro x hc hk
      rcases hk with hk | hk
      · exact (safe x hc).2.1 hk
      · exact (safe x hc).2.2.1 hk
    · intro Mx lo hdr x hin hk
      rcases hk with hk | hk
      · exact (hkoWs Mx lo hdr x hin).2.1 hk
      · exact (hkoWs Mx lo hdr x hin).2.2.1 hk
    · have hnk : ¬ KPW K Pd x := by
        rintro (hk | hk)
        · exact (hOutSafe x ho).1.2.1 hk
        · exact (hOutSafe x ho).1.2.2.1 hk
      exact (fk x (regT_out_lt reg ho) hnk).trans (fr x ho hx)

#print axioms aqgd_decCall_encReceipt_pxrB

/-- Spine drops 118-125 of the actual `process_transaction`: logs list, success flag, the receipt, and its two
words stored into the block receipt array cell `lds (bo + 32) + index * 16` (outside words in `Excl`). -/
theorem ptSufBO2 {QM : Mem → GA → Prop} (bk : BalKeep2) (Ix Rarr : BitVec 64)
    (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x) (hOut : Out w)
    -- the block receipt array cell: `bo + 32` holds `Rarr` (kept outside word), the two written words are in `Excl`
    (hBoD : D (Bo + 32)) (hBoO : Out (Bo + 32)) (hBoE : ¬ Excl (Bo + 32)) (hRarr : M0 (Bo + 32) = .word Rarr)
    (hO0 : Out (Rarr + Ix * 16) ∧ ∀ i, Rarr + Ix * 16 ≠ c i) (hE0 : Excl (Rarr + Ix * 16)) (hw0 : w ≠ Rarr + Ix * 16)
    (hO8 : Out (Rarr + Ix * 16 + 8) ∧ ∀ i, Rarr + Ix * 16 + 8 ≠ c i) (hE8 : Excl (Rarr + Ix * 16 + 8))
    (hw8 : w ≠ Rarr + Ix * 16 + 8) {cont : ProgHOL 64}
    (hcont : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => LPSo Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => LPSo Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (.seq .skip
        (.dec (ofString "logs") .one (.load .one (.op .add [(.var .local (ofString "out")),(.const 16)]))
        (.seq (.ite (.cmp .equal (.var .local (ofString "logs")) (.const 0)) (.call (some ((some (.local,ofString "logs")),none)) (ofString "lst_new") [(.const 8),(.const 1)]) .skip)
        (.dec (ofString "succeeded") .one (.const 1)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [(.var .local (ofString "out")),(.const 32)])) (.const 0)) (.assign .local (ofString "succeeded") (.const 0)) .skip)
        (.decCall (ofString "rc") (.comb [.one,.one]) (ofString "encode_receipt") [(.load .one (.op .add [(.var .local (ofString "tx")),(.const 0)])),(.var .local (ofString "succeeded")),(.load .one (.op .add [(.var .global (ofString "bo")),(.const 16)])),(.var .local (ofString "logs"))]
        (.seq (.store (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),(.const 32)])),(.panop .mul [(.var .local (ofString "index")),(.const 16)])]) (.rfield 0 (.var .local (ofString "rc"))))
        (.seq (.store (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),(.const 32)])),(.panop .mul [(.var .local (ofString "index")),(.const 16)]),(.const 8)]) (.rfield 1 (.var .local (ofString "rc"))))
        cont)))))))) := by
  have arr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc s.globals → DomD D B s →
      PXR n c T Out ko D B Excl H0 M0 s.memory s.globals →
      s.globals.lookup (ofString "bo") = some (.val (.word Bo)) ∧ s.memaddrs (Bo + 32) ∧ s.memory (Bo + 32) = .word Rarr :=
    fun s aw dom ⟨_,_,_,_,_,_,fr⟩ => ⟨aw.1.1.2,dom.2.1 ▸ hBoD,(fr _ hBoO hBoE).trans hRarr⟩
  refine aqgd_seq aqgd_skip ?_
  refine aqgd_dec_lpso _ _ _ (by decide) (by decide) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_liftB bk (by simp [keepsG,balWatched,goodBal2_lstNew]) <| aqgd_callAssign_lstNew_pxr (LP := LPSo Y Ix) _ _ _ hOut (fun h => h)
    (fun L v lp => lpso_upd lp _ v (by decide) (by decide))) aqgd_skip) ?_
  refine aqgd_dec_lpso _ _ _ (by decide) (by decide) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_assignLocal _ _ (fun s v _ _ pre _ _ =>
    ⟨lpso_upd pre.1 _ v (by decide) (by decide),pre.2⟩)) aqgd_skip) ?_
  refine aqgd_decCall_encReceipt_pxrB bk (LP' := LPRO Y Ix) _ _ _ _ _ hF hDF hcap K Pd NB hK0 hPd0 safe hOutSafe hkoWs hOut
    (fun L v lp ⟨a,b,hv⟩ => ⟨lpso_upd lp _ v (by decide) (by decide),a,b,by subst hv; exact lookup_update_eq' _ _ _⟩)
    ?_ (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq (aqgd_liftB bk (by simp [keepsG,balWatched]) <| aqgd_store_exclS (LP := LPRO Y Ix) _ _ _ (fun s aw dom lp px => ?_) (fun s x lp ev => ?_) hw0 hO0 hE0) ?_
  · obtain ⟨hb,hd,hm⟩ := arr s aw dom px
    have hd' : s.memaddrs (Bo + 32#64) := hd
    have hm' : s.memory (Bo + 32#64) = .word Rarr := hm
    have hi := lp.1.1.1
    unfold LPI at hi
    simp [EV,evalHOLExact,evalListHOLExact,hb,hd',hm',hi,memLoadHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,
      panOpHOL]
  · obtain ⟨_,a,b,he⟩ := lp
    simp [EV,evalHOLExact,he] at ev
    exact ⟨a,ev.symm⟩
  refine aqgd_seq (aqgd_liftB bk (by simp [keepsG,balWatched]) <| aqgd_store_exclS (LP := LPRO Y Ix) _ _ _ (fun s aw dom lp px => ?_) (fun s x lp ev => ?_) hw8 hO8 hE8) ?_
  · obtain ⟨hb,hd,hm⟩ := arr s aw dom px
    have hd' : s.memaddrs (Bo + 32#64) := hd
    have hm' : s.memory (Bo + 32#64) = .word Rarr := hm
    have hi := lp.1.1.1
    unfold LPI at hi
    simp [EV,evalHOLExact,evalListHOLExact,hb,hd',hm',hi,memLoadHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,
      panOpHOL,BitVec.add_assoc]
  · obtain ⟨_,a,b,he⟩ := lp
    simp [EV,evalHOLExact,he] at ev
    exact ⟨b,ev.symm⟩
  exact aqgd_conseq hcont (fun _ _ _ h => ⟨h.1.1,h.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms ptSufBO2
end cs2
end InitECandidate.Runtime
