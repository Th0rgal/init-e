import InitECandidate.Runtime.HtabDelGD
import InitECandidate.Runtime.JournalSetHeap
import InitECandidate.Runtime.OriginalHashDeleteCode
/-!
Original `jdel(t, key)` in the fixed-domain triple `AQGD` over the journal arena `JW`, on one table with the content
invariant `TCont` and `count < capacity` (explicit premises): `htab_get` (read-only), the absent-key early return,
the journal capacity guard, the key copy into a fresh allocation, the four journal-entry stores, the counter
increment, and `htab_del` through `del_aqgd_content` (globals pinned by `aqgd_fixG`). `TCont.frame`: the content
invariant survives writes outside the table's header and arrays.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The content invariant is kept by any memory change outside the table's header and five arrays. -/
theorem TCont.frame {D : BitVec 64 → Prop} {B : Bool} {M M' : Mem} {T : BitVec 64} {l : TLay}
    (tc : TCont D B M T l) (nC : l.N.toNat ≤ l.C.toNat)
    (keep : ∀ x, InTabF T l.KS l.SD l.C l.US l.VS l.OS l.OPS x → M' x = M x) : TCont D B M' T l := by
  obtain ⟨F,s,sm,sd,sb,sc,inv,oi⟩ := tc
  have rg := dreg_of_aligned inv
  have hk := rg.hk; have kb := rg.kb; have vb := rg.vb; have ub := rg.ub; have ob := rg.ob; have eb := rg.eb
  have fitT : T.toNat + 72 < 2 ^ 64 := by omega
  have k' : ∀ x, InTabF T l.KS l.SD l.C l.US l.VS l.OS l.OPS x → M' x = s.memory x := fun x h => by
    rw [sm]; exact keep x h
  refine ⟨F,{ s with memory := M' },rfl,sd,sb,sc,inv.congr rfl rfl rfl ?_ ?_,oi.congr nC rfl rfl ?_ ?_ ?_⟩
  · intro k hk64
    have e : (T + BitVec.ofNat 64 k).toNat = T.toNat + k := by
      rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
    exact k' _ (Or.inl ⟨by rw [e]; omega,by rw [e]; omega⟩)
  all_goals intro q hq
  · have := byteAlign_lt (C := l.C) rg.ua (by omega) hq
    exact k' _ (Or.inr (Or.inr (Or.inr (Or.inl this))))
  · have := byteAlign_lt (C := l.C) rg.ua (by omega) hq
    exact k' _ (Or.inr (Or.inr (Or.inr (Or.inl this))))
  · have e := add_mul8_toNat l.OS q l.C hq (by omega)
    exact k' _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [e]; omega,by rw [e]; omega⟩)))))
  · have e := add_mul8_toNat l.OPS q l.C hq (by omega)
    exact k' _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [e]; omega,by rw [e]; omega⟩)))))

#print axioms TCont.frame

variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- Pinning the globals: a triple whose arena predicate fixes the whole globals map to `G0` gives, over the plain
arena, a returned postcondition with unchanged globals. -/
theorem aqgd_fixG {G0 : GA} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64}
    (h : AQGD D B (fun g => A g ∧ g = G0) w Vn P Q RR p) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ G = G0) Q (fun v M G => RR v M G ∧ G = G0) p := by
  intro F s code dom aw sl H hH ⟨pre,hG0⟩
  have hs : s.globals = G0 := hH.trans hG0
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom ⟨aw,hs⟩ sl H hH pre
  refine ⟨m,fun cont => (a cont).1,n,fun v e => ?_,c,b⟩
  obtain ⟨H',hH',rr⟩ := r v e
  exact ⟨H',hH',rr,hH'.symm.trans (a (Or.inr (Or.inr (Or.inr ⟨v,e⟩)))).2⟩

#print axioms aqgd_fixG

/-- `jdel` locals `t`, `key`. -/
def JLd (T Kk : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "t") = some (.val (.word T)) ∧ L.lookup (ofString "key") = some (.val (.word Kk))

/-- `jdel` state after the key copy. -/
def JStd (Tk Kk J C Nj H0 : BitVec 64) (M0 : Mem) (L : GA) (M : Mem) (G : GA) : Prop :=
  JLd Tk Kk L ∧ (∃ a b : BitVec 64, L.lookup (ofString "old") = some (.rStruct [.val (.word a),.val (.word b)])) ∧
    (∃ q : BitVec 64, L.lookup (ofString "kc") = some (.val (.word q))) ∧
    (∀ x, x.toNat < H0.toNat → ¬ InJ J C x → M x = M0 x) ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ Nj.toNat < C.toNat ∧
    ∃ H2 : BitVec 64, HeapIs G H2 ∧ H0.toNat ≤ H2.toNat

/-- Exit of `jdel` on a table with content invariant: heap not below the entry heap, counter unchanged (absent key)
or incremented below the journal capacity, the table's content invariant with count kept or decremented, and memory
below the entry heap kept outside the journal buffer and the table. -/
def JDPost (D : BitVec 64 → Prop) (B : Bool) (Tk : BitVec 64) (l : TLay) (J C Nj H0 : BitVec 64) (M0 : Mem)
    (M' : Mem) (G' : GA) : Prop :=
  ∃ H' : BitVec 64, HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧
    (G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∨
      (Nj.toNat < C.toNat ∧ G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))))) ∧
    (∃ N' : BitVec 64, (N' = l.N ∨ N'.toNat + 1 = l.N.toNat) ∧
      TCont D B M' Tk ⟨l.KL,l.SD,l.C,N',l.KS,l.VS,l.US,l.OS,l.OPS,l.b⟩) ∧
    ∀ x, x.toNat < H0.toNat → ¬ InJ J C x → ¬ InTabF Tk l.KS l.SD l.C l.US l.VS l.OS l.OPS x → M' x = M0 x

variable {SP0 P0 FM : BitVec 64} {G0 : GA}

set_option maxHeartbeats 16000000 in
/-- The original `jdel(t, key)` on a table `Tk` with content invariant `TCont` and `count < capacity`, journal buffer
`[J, J + 32 C)` and counter `journal_n = Nj`: the watched word (outside the journal, below `P0`, outside the table) is
kept in every outcome; every return satisfies `JDPost`. The table lies below the entry heap and is disjoint from the
journal buffer (explicit premises). -/
theorem jdel_aqgd (Tk Kk J C Nj H0 : BitVec 64) (l : TLay) (M0 : Mem) (tc : TCont D B M0 Tk l)
    (room : l.N.toNat < l.C.toNat) (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496)
    (hwJ : ¬ InJ J C w) (hwP : w.toNat < P0.toNat) (hwT : ¬ InTabF Tk l.KS l.SD l.C l.US l.VS l.OS l.OPS w)
    (below : ∀ x, InTabF Tk l.KS l.SD l.C l.US l.VS l.OS l.OPS x → x.toNat < H0.toNat)
    (jsep : ∀ x, InJ J C x → ¬ InTabF Tk l.KS l.SD l.C l.US l.VS l.OS l.OPS x) :
    AQGD D B (JW SP0 P0 FM G0 J C) w (fun x => x ≠ ofString "old")
      (fun L M G => JLd Tk Kk L ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => JDPost D B Tk l J C Nj H0 M0 M' G')
      (sourceFunctionBody Guest.guestFn_jdel) := by
  have hdr0 : M0 (Tk + 0#64) = .word l.KL := by
    obtain ⟨F,s,sm,_,_,_,inv,_⟩ := tc; rw [← sm]; exact inv.cell0
  have hwH0 : w.toNat < H0.toNat := by omega
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_jdel,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  -- old = htab_get(t, key): read-only
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => JLd Tk Kk L ∧ (∃ a b : BitVec 64, L.lookup (ofString "old") =
        some (.rStruct [.val (.word a),.val (.word b)])) ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Qc := fun _ _ _ => True) _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => absurd rfl h) ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro L M G v M' G' ⟨⟨ht,hk⟩,rest⟩ ⟨e1,e2⟩ ok
    subst e1 e2
    obtain ⟨a,b,rfl⟩ := pair_of_shape ok
    refine ⟨⟨?_,?_⟩,⟨a,b,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rest⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  -- absent key: return 0 with nothing changed
  refine aqgd_seq (Q := fun L M G => JLd Tk Kk L ∧ (∃ a b : BitVec 64, L.lookup (ofString "old") =
        some (.rStruct [.val (.word a),.val (.word b)])) ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_return _ (fun s v H _ hG ⟨⟨_,_,hM,hH,hn⟩,_⟩ _ _ => ?_))
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h))) ?_
  · exact ⟨H0,hH,le_refl _,Or.inl hn,⟨l.N,Or.inl rfl,by rw [hM]; exact tc⟩,fun x _ _ _ => by rw [hM]⟩
  -- journal capacity guard
  refine aqgd_seq (Q := fun L M G => (JLd Tk Kk L ∧ (∃ a b : BitVec 64, L.lookup (ofString "old") =
        some (.rStruct [.val (.word a),.val (.word b)])) ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj))) ∧ Nj.toNat < C.toNat)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => Nj.toNat < C.toNat) _ ?_ (aqgd_of_aqg (aqg_trapCall 5))
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  · intro F s x G ⟨_,_,hcap⟩ hG ⟨_,_,_,_,hn⟩ _ ev
    unfold GIs at hG; subst hG
    refine ⟨fun _ => trivial,fun hx => ?_⟩
    subst hx
    simp [EV,evalHOLExact,hn,hcap,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at ev
    exact BitVec.lt_def.mp ev
  -- klen = lds (t + 0)
  refine aqgd_dec (Pb := fun L M G => (JLd Tk Kk L ∧ (∃ a b : BitVec 64, L.lookup (ofString "old") =
        some (.rStruct [.val (.word a),.val (.word b)])) ∧
        L.lookup (ofString "klen") = some (.val (.word l.KL))) ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ Nj.toNat < C.toNat)
    (Qb := fun _ _ _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v G _ hG ⟨⟨⟨ht,hk⟩,⟨a,b,ho⟩,hM,hH,hn⟩,hlt⟩ _ ev _
    rw [ev_load_off s _ Tk 0#64 v ht ev,show s.memory (Tk + 0#64) = .word l.KL by rw [hM]; exact hdr0]
    refine ⟨⟨⟨?_,?_⟩,⟨a,b,?_⟩,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,hM,hH,hn,hlt⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  -- kc = alloc(klen)
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' _ L M G => G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H, HeapIs G H ∧
      (L.lookup (ofString "n") = some (.val (.word l.KL)) ∧ M = M0' ∧ H = H0))
    (RRe := fun _ M0' _ v M' G' => G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H', HeapIs G' H' ∧
      (M' = M0' ∧ v = .val (.word H0) ∧ H' = allocationEnd H0 l.KL ∧ P0.toNat ≤ H0.toNat ∧
        H0.toNat + l.KL.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧ H'.toNat % 8 = 0 ∧ H0.toNat % 8 = 0))
    (Pc := fun L M G => (JLd Tk Kk L ∧ (∃ a b : BitVec 64, L.lookup (ofString "old") =
        some (.rStruct [.val (.word a),.val (.word b)])) ∧
        L.lookup (ofString "klen") = some (.val (.word l.KL)) ∧
        L.lookup (ofString "kc") = some (.val (.word H0))) ∧ M = M0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ Nj.toNat < C.toNat ∧ H0.toNat % 8 = 0 ∧
        ∃ H2 : BitVec 64, HeapIs G H2 ∧ H0.toNat + l.KL.toNat ≤ H2.toNat ∧ H2.toNat ≤ 33806089496)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' _ _ => aqgd_of_aqg (aqg_conseq (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_allocation_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) l.KL H0 M0'))
      (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)))
    ?_ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ G hG ⟨⟨_,_,hkl⟩,_,hH,hn,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,hkl] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨hn,H0,hH,by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨ht,hk⟩,⟨a,b,ho⟩,hkl⟩,hM,_,_,hlt⟩ ⟨hn',H',hH',eM,ev,_,_,c1,fin,_,al⟩ _
    subst eM ev
    refine ⟨⟨⟨?_,?_⟩,⟨a,b,?_⟩,?_,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,hM,hn',hlt,al,H',hH',c1,fin⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  -- memcpy(kc, key, klen): only the fresh key copy changes
  refine aqgd_seq (Q := fun L M G => JStd Tk Kk J C Nj H0 M0 L M G)
    (aqgd_callSpec (Vn' := fun _ => False)
      (Pe := fun _ M0' G0' L M G => (L.lookup (ofString "dst") = some (.val (.word H0)) ∧
        L.lookup (ofString "src") = some (.val (.word Kk)) ∧
        L.lookup (ofString "n") = some (.val (.word l.KL))) ∧ M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' _ M' G' => G' = G0' ∧ ∀ x, ¬ MWin H0 l.KL.toNat x → M' x = M0' x)
      _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_) ?_
  · intro L0 M0' G0' ⟨_,_,_,_,al,H2,_,c1,fin⟩
    have small : l.KL.toNat + 32 < 2 ^ 64 := by omega
    exact aqgd_of_window memcpy_body_globals_frame (by body_check Guest.guestFn_memcpy)
      (by body_check Guest.guestFn_memcpy) (MWin H0 l.KL.toNat)
      (fun s _ ⟨hd,hs,hn⟩ x hx => memcpy_body_window s H0 Kk l.KL x hd hs hn small hx)
      (mwin_above hwH0 al (by omega)) M0' G0'
  · intro F s values callee rs _ G hG ⟨⟨⟨ht,hk⟩,_,hkl,hkc⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hkc,hk,hkl] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_memcpy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨hjl,hold,_,hkc⟩,hM,hn,hlt,al,H2,hH2,c1,fin⟩ ⟨eG,fr⟩
    subst eG hM
    refine ⟨hjl,hold,⟨H0,hkc⟩,fun x hx _ => fr x (fun hw' => ?_),hn,hlt,H2,hH2,by omega⟩
    have := (mwin_ge hw' al (by omega)).1
    omega
  -- r = journal + journal_n * 32
  refine aqgd_dec (Pb := fun L M G => JStd Tk Kk J C Nj H0 M0 L M G ∧
      L.lookup (ofString "r") = some (.val (.word (J + Nj * 32#64))))
    (Qb := fun _ _ _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v G aw hG ⟨⟨ht,hk⟩,⟨a,b,ho⟩,⟨q,hq⟩,fr,hn,hlt,hH⟩ _ ev _
    unfold GIs at hG; subst hG
    have hj := aw.2.1
    simp [EV,evalHOLExact,evalListHOLExact,hj,hn,panOpHOL,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    refine ⟨⟨⟨?_,?_⟩,⟨a,b,?_⟩,⟨q,?_⟩,fr,hn,hlt,hH⟩,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  -- the journal entry: four word stores inside [J + 32 Nj, J + 32 Nj + 32)
  have jst : ∀ (d v : ExpHOL 64) (o : BitVec 64), o.toNat < 32 →
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
        s.locals.lookup (ofString "r") = some (.val (.word (J + Nj * 32#64))) →
        EV s d = some (.val (.word (J + Nj * 32#64 + o)))) →
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, JStd Tk Kk J C Nj H0 M0 s.locals s.memory s.globals →
        EV s v = some x → ∃ y : BitVec 64, x = .val (.word y)) →
      AQGD D B (JW SP0 P0 FM G0 J C) w (fun x => x ≠ ofString "old")
        (fun L M G => JStd Tk Kk J C Nj H0 M0 L M G ∧
          L.lookup (ofString "r") = some (.val (.word (J + Nj * 32#64))))
        (fun L M G => JStd Tk Kk J C Nj H0 M0 L M G ∧
          L.lookup (ofString "r") = some (.val (.word (J + Nj * 32#64))))
        (fun _ M' G' => JDPost D B Tk l J C Nj H0 M0 M' G')
        (.store d v) := by
    intro d v o ho hd hv
    refine aqgd_store _ _ (fun s G _ hG ⟨st,hr⟩ _ => ?_) (fun s x G _ hG ⟨st,_⟩ _ ev => ?_)
    · unfold GIs at hG; subst hG
      obtain ⟨hjl,hold,hkc,fr,hn,hlt,hH⟩ := st
      obtain ⟨inj,_⟩ := inj_entry (o := o) hlt jfit ho
      refine ⟨_,hd s hr,fun e => hwJ (e ▸ inj),fun y _ => ⟨⟨hjl,hold,hkc,fun x hx hnj => ?_,hn,hlt,hH⟩,hr⟩⟩
      have : x ≠ J + Nj * 32#64 + o := fun e => hnj (e ▸ inj)
      simp only [if_neg this]
      exact fr x hx hnj
    · unfold GIs at hG; subst hG
      exact hv s x st ev
  refine aqgd_seq (jst _ _ 0#64 (by decide) (fun s hr => by simp [EV,evalHOLExact,hr])
    (fun s x ⟨⟨ht,_⟩,_⟩ ev => by simp [EV,evalHOLExact,ht] at ev; exact ⟨_,ev.symm⟩)) ?_
  refine aqgd_seq (jst _ _ 8#64 (by decide)
    (fun s hr => by simp [EV,evalHOLExact,evalListHOLExact,hr,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨_,_,⟨q,hq⟩,_⟩ ev => by simp [EV,evalHOLExact,hq] at ev; exact ⟨_,ev.symm⟩)) ?_
  refine aqgd_seq (jst _ _ 16#64 (by decide)
    (fun s hr => by simp [EV,evalHOLExact,evalListHOLExact,hr,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x _ ev => by simp [EV,evalHOLExact] at ev; exact ⟨_,ev.symm⟩)) ?_
  refine aqgd_seq (jst _ _ 24#64 (by decide)
    (fun s hr => by simp [EV,evalHOLExact,evalListHOLExact,hr,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨_,⟨a,b,ho⟩,_⟩ ev => by simp [EV,evalHOLExact,ho] at ev; exact ⟨_,ev.symm⟩)) ?_
  -- journal_n = journal_n + 1
  refine aqgd_seq (Q := fun L M G => JLd Tk Kk L ∧ (∀ x, x.toNat < H0.toNat → ¬ InJ J C x → M x = M0 x) ∧
      G.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧ Nj.toNat < C.toNat ∧
      ∃ H2 : BitVec 64, HeapIs G H2 ∧ H0.toNat ≤ H2.toNat)
    (aqgd_assignGlobal _ _ (fun s v aw ⟨⟨hjl,_,_,fr,hn,hlt,H2,hH2,hle⟩,_⟩ _ ev => ?_)) ?_
  · simp [EV,evalHOLExact,evalListHOLExact,hn,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    refine ⟨jw_update_n aw _,hjl,fr,by simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],hlt,H2,?_,hle⟩
    have ne : ofString "journal_n" ≠ ofString "heap_ptr" := by decide
    unfold HeapIs at hH2 ⊢
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne,hH2]
  -- htab_del(t, key) on the table, whose content invariant survives the journal and key-copy writes
  refine aqgd_seq (Q := fun _ M' G' => JDPost D B Tk l J C Nj H0 M0 M' G')
    (aqgd_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' G0' L M G => (LK [(ofString "key",Kk),(ofString "t",Tk)] L ∧ M = M0') ∧ G = G0')
      (RRe := fun _ M0' G0' _ M' G' => (∃ N' : BitVec 64, (N' = l.N ∨ N'.toNat + 1 = l.N.toNat) ∧
          TCont D B M' Tk ⟨l.KL,l.SD,l.C,N',l.KS,l.VS,l.US,l.OS,l.OPS,l.b⟩ ∧
          ∀ x, ¬ InTabF Tk l.KS l.SD l.C l.US l.VS l.OS l.OPS x → M' x = M0' x) ∧ G' = G0')
      _ _ _ _ _ originalRuntimeCode_hashDelete_lookup (by simp) ?_ ?_ ?_)
    (aqgd_return _ (fun _ _ _ _ _ h _ _ => h))
  · intro L0 M0' G0' ⟨_,fr,_,_,_⟩
    have tc1 : TCont D B M0' Tk l := tc.frame room.le (fun x hx => fr x (below x hx) (fun hj => jsep x hj hx))
    exact aqgd_fixG (del_aqgd_content Kk tc1 room hwT)
  · intro F s values callee rs _ G hG ⟨⟨ht,hk⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,ht,hk] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_hashDelete_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨⟨fun p hp => ?_,rfl⟩,rfl⟩
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨_,fr,hn1,hlt,H2,hH2,hle⟩ ⟨⟨N',hN',tc',fr'⟩,eG⟩
    subst eG
    exact ⟨H2,hH2,hle,Or.inr ⟨hlt,hn1⟩,⟨N',hN',tc'⟩,fun x hx hnj hnt => (fr' x hnt).trans (fr x hx hnj)⟩

#print axioms jdel_aqgd
end InitECandidate.Runtime
