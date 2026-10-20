import InitECandidate.Runtime.PtAwInvGD
import InitECandidate.Runtime.DestroyAccountGD
/-!
The actual `destroy_account(addr)` (`destroy_storage(addr); set_account(addr, 1)`) keeps the accounts-written table
ready (`AwIL`): `destroy_storage` runs over the registry restricted to the other tables, with the table's cell and
region as outside words (kept by its exit frame); `set_account` is the content-preserving `jset`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem destroyAccount_body_eq : sourceFunctionBody Guest.guestFn_destroy_account =
    (ProgHOL.call (some (none, none)) (ofString "destroy_storage") [ExpHOL.var VarKind.local (ofString "addr")]).seq
      ((ProgHOL.call (some (none, none)) (ofString "set_account")
            [ExpHOL.var VarKind.local (ofString "addr"), ExpHOL.const 1#64]).seq
        (ProgHOL.return (ExpHOL.const 0#64))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_destroy_account,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]

/-- Exit of an accounts-written table writer: the heap pointer up from `H0`, some journal counter, the table ready with
some layout at the exit heap pointer. -/
def AwPost (m : Nat) (c' T' : Fin m → BitVec 64) (ko' : Fin m) (Out : BitVec 64 → Prop) (D : BitVec 64 → Prop)
    (B : Bool) (J C SKB Ts Taw : BitVec 64) (S : Set (BitVec 64)) (H0 : BitVec 64) (M' : Mem) (G' : GA) : Prop :=
  ∃ (la' : TLay) (Hp Nj' : BitVec 64), HeapIs G' Hp ∧ H0.toNat ≤ Hp.toNat ∧
    G'.lookup (ofString "journal_n") = some (.val (.word Nj')) ∧ AwIL m c' T' ko' Out D B J C SKB Ts Taw S la' Hp Hp M'

section da
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM : BitVec 64} {G0 : GA}
  {J C SKB Bo U Sc : BitVec 64} {m : Nat} {c' T' : Fin m → BitVec 64} {ko' kd' : Fin m} {Out : BitVec 64 → Prop}
  {S : Set (BitVec 64)}

/-- `set_account(addr, V)` as a call statement on the table under `AwIL`. -/
theorem aqgd_call_setAccount_aw {LP : GA → Prop} (eA eV : ExpHOL 64) (Ts Taw A V Nj H1 Hl : BitVec 64) (la : TLay)
    (M1 : Mem) (G1 : GA) (hAB : kd' ≠ ko')
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (aw : AwIL m c' T' ko' Out D B J C SKB Ts Taw S la Hl H1 M1) (hH1 : HeapIs G1 H1)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (p0 : P0.toNat ≤ H1.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hJO : ∀ x, InJ J C x → Out x) (jcell : ∀ x, InJ J C x → ∀ i, x ≠ c' i)
    (jB : J.toNat + C.toNat * 32 ≤ H1.toNat) (skB : ∀ x, SkWin SKB x → x.toNat < H1.toNat)
    (outB : ∀ x, Out x → x.toNat < H1.toNat) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) (hV : V ∈ S)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [eA,eV] =
        some [.val (.word A),.val (.word V)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ AwPost m c' T' ko' Out D B J C SKB Ts Taw S H1 M G) (fun _ _ _ => False)
      (.call (some (none,none)) (ofString "set_account") [eA,eV]) := by
  have aw0 := aw
  obtain ⟨⟨rv,hl,cell,sup,sd⟩,_,sep,oT,_⟩ := aw0
  have below : ∀ x, TabPhys Taw la x → x.toNat < H1.toNat := fun x hx => (sep x (Or.inr hx)).1
  have jsep : ∀ x, InJ J C x → ¬ TabPhys Taw la x := fun x hj hx => (sep x (Or.inr hx)).2.1 hj
  refine aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => (L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "a") = some (.val (.word V))) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ _ _ _ M' G' => JSRV D B Taw la S J C Nj H1 M1 M' G')
    _ _ _ _ _ originalRuntimeCode_setAccount_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst hM hG
    exact aqgd_conseq (setAccount_rv_aqgd Ts Taw A V Nj H1 Hl la S M0' hTs cell rv hl below jsep p0 jfit hwJ hwP
      (oT w hOut) Dall sup sd hV hK hKE) (fun L M G ⟨lk,hM,hG⟩ => ⟨lk,hM,by rw [hG]; exact hH1,by rw [hG]; exact hn1⟩)
      (fun _ _ _ _ => trivial) (fun _ _ _ h => h)
  · intro F s values callee rs _ G hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_setAccount_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,_⟩ js
    subst hM
    obtain ⟨la',Hp,hHp,hle,hn',_,aw'⟩ := awIL_jset hAB aw hJO jcell jB skB outB js
    exact ⟨lp,la',Hp,Nj + 1,hHp,hle,hn',aw'⟩

#print axioms aqgd_call_setAccount_aw
/-- `destroy_storage(e)` as a call statement under `AwIL`, over the restricted registry. -/
theorem aqgd_call_destroyStorage_aw {LP : GA → Prop} (eA : ExpHOL 64) (Ts Taw Nj H1 Hl : BitVec 64) (la : TLay)
    (M1 : Mem) (G1 : GA) (ne : kd' ≠ ko')
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hco : c' ko' = Ts + 32#64)
    (hcd : c' kd' = Ts + 24#64)
    (aw : AwIL m c' T' ko' Out D B J C SKB Ts Taw S la Hl H1 M1) (hH1 : HeapIs G1 H1)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (p0 : P0.toNat ≤ H1.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c' i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c' i ∧ ¬ HdrR (T' i) x)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals →
      ∃ A : BitVec 64, evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [eA] =
        some [.val (.word A)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ ∃ H' Nj' : BitVec 64, HeapIs G H' ∧ H1.toNat ≤ H'.toNat ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj')) ∧
        AwIL m c' T' ko' Out D B J C SKB Ts Taw S la Hl H' M) (fun _ _ _ => False)
      (.call (some (none,none)) (ofString "destroy_storage") [eA]) := by
  have reg := aw.2.1
  refine aqgd_callSpec (Vn' := fun x => x ≠ ofString "m" ∧ x ≠ ofString "s")
    (Pe := fun _ M0' _ L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      RegT m c' T' (fun x => Out x ∨ AwFp Ts Taw la x) H1 M D B ko' ∧ M = M0' ∧ HeapIs G H1 ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (RRe := fun _ M0' _ _ M' G' => DSPost m c' T' (fun x => Out x ∨ AwFp Ts Taw la x) ko' D B J C SKB H1 Nj M0' M' G')
    _ _ _ _ _ originalRuntimeCode_destroyStorage_lookup (by simp)
    (fun _ M0' _ _ => aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc)
      (destroyStorage_aqgd (M0 := M0') ne hTs hco hcd p0 jfit hwJ hwP (Or.inl hOut) hwS
        (fun x hx => Or.inl (hJO x hx)) (fun x hx => ⟨Or.inl (hSO x hx).1,(hSO x hx).2⟩) jsep)
      (keepsBo_of_installed originalRuntimeCode_destroyStorage_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_destroyStorage_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_destroyStorage_lookup (by decide))) ?_ ?_
  · intro F s values callee rs _ G hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨A,hA⟩ := hargs s lp
    rw [hA] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_destroyStorage_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,by rw [hM]; exact reg,rfl,by rw [hG1]; exact hH1,
      by rw [hG1]; exact hn1⟩
  · intro L M G v M' G' ⟨lp,hM,_⟩ ⟨H',hH',hle,reg',hn',fr⟩
    subst hM
    rcases hn' with h | ⟨_,h⟩
    · exact ⟨lp,H',Nj,hH',hle,h,awIL_frame aw reg' hle fr⟩
    · exact ⟨lp,H',Nj + 1,hH',hle,h,awIL_frame aw reg' hle fr⟩

#print axioms aqgd_call_destroyStorage_aw
/-- The actual `destroy_account(addr)` body under `AwIL`: the table stays ready (`AwPost`). -/
theorem destroyAccount_rv_aqgd (Ts Taw A Nj H1 Hl : BitVec 64) (la : TLay) (M1 : Mem) (ne : kd' ≠ ko')
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hco : c' ko' = Ts + 32#64)
    (hcd : c' kd' = Ts + 24#64)
    (aw : AwIL m c' T' ko' Out D B J C SKB Ts Taw S la Hl H1 M1)
    (p0 : P0.toNat ≤ H1.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c' i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c' i ∧ ¬ HdrR (T' i) x)
    (jB : J.toNat + C.toNat * 32 ≤ P0.toNat) (outB : ∀ x, Out x → x.toNat < P0.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) (h1 : 1#64 ∈ S)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => L.lookup (ofString "addr") = some (.val (.word A)) ∧ (M = M1 ∧ HeapIs G H1 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj))))
      (fun _ _ _ => True) (fun _ M' G' => AwPost m c' T' ko' Out D B J C SKB Ts Taw S H1 M' G')
      (sourceFunctionBody Guest.guestFn_destroy_account) := by
  rw [destroyAccount_body_eq]
  have jcell : ∀ x, InJ J C x → ∀ i, x ≠ c' i := fun x hj i => (jsep x hj i).1
  refine aqgd_ghostJ (fun M2 G2 ⟨hM,hH,hn⟩ => ?_)
  subst hM
  refine aqgd_seq (aqgd_conseq (aqgd_call_destroyStorage_aw
    (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)))
    (.var .local (ofString "addr")) Ts Taw Nj H1 Hl la M2 G2 ne hTs hco hcd aw hH hn p0 jfit hwJ hwP hOut hwS hJO hSO
    jsep (fun s lp => ⟨A,by rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,lp]⟩))
    (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.elim)) ?_
  refine aqgd_conseq (P := fun L M G => ∃ q : BitVec 64 × BitVec 64, L.lookup (ofString "addr") =
      some (.val (.word A)) ∧ (HeapIs G q.1 ∧ H1.toNat ≤ q.1.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word q.2)) ∧ AwIL m c' T' ko' Out D B J C SKB Ts Taw S la Hl q.1 M))
    (aqgd_ex (fun q => ?_)) (fun L M G ⟨lp,H',Nj',hH',hle,hn',aw'⟩ => ⟨(H',Nj'),lp,hH',hle,hn',aw'⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  rcases q with ⟨H',Nj'⟩
  dsimp only
  refine aqgd_ghostJ (fun M3 G3 ⟨hH',hle,hn',aw'⟩ => ?_)
  have skB : ∀ x, SkWin SKB x → x.toNat < H'.toNat := fun x hs => by have := outB x (hSO x hs).1; omega
  refine aqgd_seq (aqgd_conseq (aqgd_call_setAccount_aw
    (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)))
    (.var .local (ofString "addr")) (.const 1#64) Ts Taw A 1#64 Nj' H' Hl la M3 G3 ne hTs aw' hH' hn' (by omega) jfit
    hwJ hwP hOut hJO jcell (by omega) skB (fun x ho => by have := outB x ho; omega) Dall h1 hK hKE
    (fun s lp => by rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,lp]))
    (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.elim)) ?_
  exact aqgd_return _ (fun s v G _ hG ⟨_,la',Hp,Nj'',hHp,hle',hn'',aw''⟩ _ _ => by
    unfold GIs at hG; subst hG
    exact ⟨la',Hp,Nj'',hHp,by omega,hn'',aw''⟩)

#print axioms destroyAccount_rv_aqgd
end da
end InitECandidate.Runtime
