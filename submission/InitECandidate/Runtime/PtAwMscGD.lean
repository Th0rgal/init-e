import InitECandidate.Runtime.PtAwDestroyGD
import InitECandidate.Runtime.ModifyStateCommitGD
/-!
The actual `modify_state_commit(addr, a)` (`set_account(addr, a)`, read-only `acct_is_empty(a)`, and for an empty
account `destroy_account(addr)`) keeps the accounts-written table ready (`AwPost`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem msc_body_eq : sourceFunctionBody Guest.guestFn_modify_state_commit =
    (ProgHOL.call (some (none, none)) (ofString "set_account")
        [ExpHOL.var VarKind.local (ofString "addr"), ExpHOL.var VarKind.local (ofString "a")]).seq
      (ProgHOL.decCall (ofString "e") ShapeHOL.one (ofString "acct_is_empty") [ExpHOL.var VarKind.local (ofString "a")]
        ((ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "e")) (ExpHOL.const 0#64))
              (ProgHOL.call (some (none, none)) (ofString "destroy_account")
                [ExpHOL.var VarKind.local (ofString "addr")])
              ProgHOL.skip).seq
          (ProgHOL.return (ExpHOL.const 0#64)))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_modify_state_commit,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]

section ms
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM : BitVec 64} {G0 : GA}
  {J C SKB Bo U Sc : BitVec 64} {m : Nat} {c' T' : Fin m → BitVec 64} {ko' kd' : Fin m} {Out : BitVec 64 → Prop}
  {S : Set (BitVec 64)}

theorem awPost_mono {Ts Taw H0 H1 : BitVec 64} {M : Mem} {G : GA}
    (h : AwPost m c' T' ko' Out D B J C SKB Ts Taw S H1 M G) (le : H0.toNat ≤ H1.toNat) :
    AwPost m c' T' ko' Out D B J C SKB Ts Taw S H0 M G :=
  let ⟨la',Hp,Nj',hH,hle,hn,aw⟩ := h; ⟨la',Hp,Nj',hH,by omega,hn,aw⟩

/-- `destroy_account(e)` as a call statement under `AwIL`. -/
theorem aqgd_call_destroyAccount_aw {LP : GA → Prop} (eA : ExpHOL 64) (Ts Taw A Nj H1 Hl : BitVec 64) (la : TLay)
    (M1 : Mem) (G1 : GA) (ne : kd' ≠ ko')
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hco : c' ko' = Ts + 32#64)
    (hcd : c' kd' = Ts + 24#64)
    (aw : AwIL m c' T' ko' Out D B J C SKB Ts Taw S la Hl H1 M1) (hH1 : HeapIs G1 H1)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (p0 : P0.toNat ≤ H1.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c' i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c' i ∧ ¬ HdrR (T' i) x)
    (jB : J.toNat + C.toNat * 32 ≤ P0.toNat) (outB : ∀ x, Out x → x.toNat < P0.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) (h1 : 1#64 ∈ S)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [eA] = some [.val (.word A)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ AwPost m c' T' ko' Out D B J C SKB Ts Taw S H1 M G) (fun _ _ _ => False)
      (.call (some (none,none)) (ofString "destroy_account") [eA]) := by
  refine aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' _ L M G => L.lookup (ofString "addr") = some (.val (.word A)) ∧ (M = M0' ∧ HeapIs G H1 ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj))))
    (RRe := fun _ _ _ _ M' G' => AwPost m c' T' ko' Out D B J C SKB Ts Taw S H1 M' G')
    _ _ _ _ _ originalRuntimeCode_destroyAccount_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hM,_⟩
    subst hM
    exact destroyAccount_rv_aqgd Ts Taw A Nj H1 Hl la M0' ne hTs hco hcd aw p0 jfit hwJ hwP hOut hwS hJO hSO jsep jB
      outB Dall h1 hK hKE
  · intro F s values callee rs _ G hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_destroyAccount_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,by rw [hG1]; exact hH1,by rw [hG1]; exact hn1⟩
  · intro L M G v M' G' ⟨lp,_,_⟩ post
    exact ⟨lp,post⟩

#print axioms aqgd_call_destroyAccount_aw
/-- The actual `modify_state_commit(addr, a)` body under `AwIL`: the table stays ready (`AwPost`). -/
theorem msc_rv_aqgd (Ts Taw A V Nj H1 Hl : BitVec 64) (la : TLay) (M1 : Mem) (ne : kd' ≠ ko')
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hco : c' ko' = Ts + 32#64)
    (hcd : c' kd' = Ts + 24#64)
    (aw : AwIL m c' T' ko' Out D B J C SKB Ts Taw S la Hl H1 M1)
    (p0 : P0.toNat ≤ H1.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c' i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c' i ∧ ¬ HdrR (T' i) x)
    (jB : J.toNat + C.toNat * 32 ≤ P0.toNat) (outB : ∀ x, Out x → x.toNat < P0.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) (h1 : 1#64 ∈ S) (hV : V ∈ S)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (L.lookup (ofString "addr") = some (.val (.word A)) ∧
        L.lookup (ofString "a") = some (.val (.word V))) ∧ (M = M1 ∧ HeapIs G H1 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj))))
      (fun _ _ _ => True) (fun _ M' G' => AwPost m c' T' ko' Out D B J C SKB Ts Taw S H1 M' G')
      (sourceFunctionBody Guest.guestFn_modify_state_commit) := by
  rw [msc_body_eq]
  have jcell : ∀ x, InJ J C x → ∀ i, x ≠ c' i := fun x hj i => (jsep x hj i).1
  have skB : ∀ x, SkWin SKB x → x.toNat < H1.toNat := fun x hs => by have := outB x (hSO x hs).1; omega
  refine aqgd_ghostJ (fun M2 G2 ⟨hM,hH,hn⟩ => ?_)
  subst hM
  refine aqgd_seq (aqgd_conseq (aqgd_call_setAccount_aw
    (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "a") = some (.val (.word V)))
    (.var .local (ofString "addr")) (.var .local (ofString "a")) Ts Taw A V Nj H1 Hl la M2 G2 ne hTs aw hH hn p0 jfit
    hwJ hwP hOut hJO jcell (by omega) skB (fun x ho => by have := outB x ho; omega) Dall hV hK hKE
    (fun s lp => by rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,lp.1,lp.2]))
    (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.elim)) ?_
  -- e = acct_is_empty(a): read-only
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => L.lookup (ofString "addr") = some (.val (.word A)) ∧
      AwPost m c' T' ko' Out D B J C SKB Ts Taw S H1 M G) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_acctIsEmpty_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf acctIsEmpty_mf (by body_check Guest.guestFn_acct_is_empty)
      (by body_check Guest.guestFn_acct_is_empty) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨ha,_⟩,wp⟩ ⟨e1,e2⟩ _
    subst e1 e2
    exact ⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,ha],wp⟩
  -- an empty account is destroyed
  refine aqgd_seq (Q := fun _ M G => AwPost m c' T' ko' Out D B J C SKB Ts Taw S H1 M G)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => h.1.2) (fun _ _ _ h => h)))
    (aqgd_return _ (fun _ _ _ _ hG h _ _ => by unfold GIs at hG; subst hG; exact h))
  refine aqgd_conseq (P := fun L M G => ∃ q : TLay × BitVec 64 × BitVec 64,
      L.lookup (ofString "addr") = some (.val (.word A)) ∧ (HeapIs G q.2.1 ∧ H1.toNat ≤ q.2.1.toNat ∧
      G.lookup (ofString "journal_n") = some (.val (.word q.2.2)) ∧
      AwIL m c' T' ko' Out D B J C SKB Ts Taw S q.1 q.2.1 q.2.1 M))
    (aqgd_ex (fun q => ?_)) (fun L M G ⟨⟨ha,la',Hp,Nj',hHp,hle,hn',aw'⟩,_⟩ => ⟨(la',Hp,Nj'),ha,hHp,hle,hn',aw'⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  rcases q with ⟨la',Hp,Nj'⟩
  dsimp only
  refine aqgd_ghostJ (fun M3 G3 ⟨hHp,hle,hn',aw'⟩ => ?_)
  exact aqgd_conseq (aqgd_call_destroyAccount_aw (LP := fun L => L.lookup (ofString "addr") = some (.val (.word A)))
    (.var .local (ofString "addr")) Ts Taw A Nj' Hp Hp la' M3 G3 ne hTs hco hcd aw' hHp hn' (by omega) jfit hwJ hwP
    hOut hwS hJO hSO jsep jB outB Dall h1 hK hKE
    (fun s lp => by rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,lp]))
    (fun _ _ _ h => h) (fun _ _ _ ⟨_,post⟩ => awPost_mono post hle) (fun _ _ _ h => h.elim)

#print axioms msc_rv_aqgd
end ms
end InitECandidate.Runtime
