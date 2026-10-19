import InitECandidate.Runtime.JournalSetHeap
import InitECandidate.Runtime.OriginalJournalSetCode
import InitECandidate.Runtime.OriginalStateCommitCode
import InitECandidate.Runtime.EvmDispatchHeap
/-!
Heap- and globals-aware original account writers over a table registry: `set_account` (`jset` on `ts + 16`),
`modify_state_commit` (with `acct_is_empty` read-only and the `destroy_account` contract `DestroyContract` as an
explicit hypothesis), `acct_copy`, `increment_nonce` and `set_account_balance` (with `get_account`'s per-word frames
combined by `aqmh_family_frame`).  Every return re-establishes the registry and keeps the outside words not in the
journal buffer or the destroy region.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {A : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}

theorem aqg_ex {α : Sort _} {P : α → HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    {Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {p : ProgHOL 64}
    (h : ∀ a, AQG A w Vn (P a) Q RR p) : AQG A w Vn (fun L M G => ∃ a, P a L M G) Q RR p :=
  fun F s code dom aw sl G hG ⟨a,pre⟩ => h a F s code dom aw sl G hG pre

variable {SP0 P0 FM : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)}

set_option maxHeartbeats 4000000 in
/-- `jset` over a registry with outside words `Out`: every return re-establishes the registry at the exit heap and
keeps every outside word that is not in the journal buffer. -/
theorem jsetReg_aqg (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (k : Fin n) (Kk V J C Nj H0 : BitVec 64)
    (M0 : Mem) (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) :
    AQG (JW SP0 P0 FM G0 J C) w (fun x => x ≠ ofString "old")
      (fun L M G => JL (T k) Kk V L ∧ Reg n c T Out H0 M ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True)
      (fun _ M' G' => Nj.toNat < C.toNat ∧ G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧
        ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧
          ∀ x, Out x → ¬ InJ J C x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_jset) := by
  refine aqg_conseq (P := fun L M G => ∃ l : Fin n → TLay, RegPure n c T Out H0 l ∧ (JL (T k) Kk V L ∧
      RegMem n c T l M ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))))
    (aqg_ex (fun l => ?_)) (fun L M G ⟨hj,⟨l,tA,sep,o⟩,hm,hh,hn⟩ => ⟨l,⟨fun i => ⟨(tA i).2.1,(tA i).2.2.2⟩,sep,o⟩,hj,
      fun i => ⟨(tA i).1,(tA i).2.2.1⟩,hm,hh,hn⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  intro F s code dom aw sl G hG ⟨pure,pre⟩
  have hm0 : RegMem n c T l M0 := pre.2.2.1 ▸ pre.2.1
  obtain ⟨m,a,nn,r,cc,b⟩ := jset_aqg n c T Out l k H0 pure Kk V J C Nj M0 hm0 p0 jfit hwJ hwP hOut jsep
    F s code dom aw sl G hG pre
  refine ⟨m,a,nn,fun v e => ?_,cc,b⟩
  obtain ⟨G',hG',hlt,hn,H',hH',hle,reg,fr⟩ := r v e
  refine ⟨G',hG',hlt,hn,H',hH',hle,reg,fun x hx hnj => fr x ?_ hnj (pure.2.2 x hx k)⟩
  by_contra c'
  exact pure.2.2 x hx k (Or.inr (Or.inr (by omega)))

#print axioms jsetReg_aqg

/-- Post-state of the account writers: registry at the exit heap, outside words kept unless in the journal. -/
def WPost (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (J C H0 : BitVec 64) (M0 : Mem) (M' : Mem)
    (G' : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧ ∀ x, Out x → ¬ InJ J C x → M' x = M0 x

set_option maxHeartbeats 4000000 in
/-- `set_account(addr, a)`: `jset` on the account table at `ts + 16` (registry index `k`). -/
theorem setAccount_aqg (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (k : Fin n) (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hck : c k = Ts + 16#64) (J C Nj H0 : BitVec 64)
    (M0 : Mem) (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) :
    AQG (JW SP0 P0 FM G0 J C) w (fun _ => True)
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ Reg n c T Out H0 M ∧ M = M0 ∧
        HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True)
      (fun _ M' G' => Nj.toNat < C.toNat ∧ G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧
        WPost n c T Out J C H0 M0 M' G')
      (sourceFunctionBody Guest.guestFn_set_account) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_set_account,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  refine aqg_seq (Q := fun _ M' G' => Nj.toNat < C.toNat ∧
      G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧ WPost n c T Out J C H0 M0 M' G')
    (aqg_callSpec (Vn' := fun x => x ≠ ofString "old")
      (Pe := fun _ M0' G0' L M G => (∃ Kk V : BitVec 64, JL (T k) Kk V L) ∧ M = M0' ∧ G = G0')
      (RRe := fun _ M0' _ _ M' G' => Nj.toNat < C.toNat ∧
        G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧ WPost n c T Out J C H0 M0' M' G')
      _ _ _ _ _ originalRuntimeCode_journalSet_lookup (by simp) ?_ ?_
      (fun _ _ _ _ _ _ ⟨_,_,_,hM,_,_⟩ h => by subst hM; exact h))
    (aqg_return _ (fun _ _ _ _ _ h _ _ => h))
  · intro L0 M0' G0' ⟨_,_,reg,_,hH,hn⟩
    refine aqg_conseq (P := fun L M G => ∃ Kk, ∃ V, JL (T k) Kk V L ∧ Reg n c T Out H0 M ∧ M = M0' ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (aqg_ex (fun Kk => aqg_ex (fun V => jsetReg_aqg n c T Out k Kk V J C Nj H0 M0' p0 jfit hwJ hwP hOut jsep)))
      ?_ (fun _ _ _ _ => trivial) (fun v M' G' ⟨h1,h2,H',h3,h4,h5,h6⟩ => ⟨h1,h2,H',h3,h4,h5,h6⟩)
    intro L M G ⟨⟨Kk,V,hj⟩,hM,hG⟩
    subst hM hG
    exact ⟨Kk,V,hj,reg,rfl,hH,hn⟩
  · intro F s values callee rs aw G hG ⟨⟨A,hA⟩,⟨V,hV⟩,⟨l,tA,_,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨eg,_⟩ := aw.1.2.2.2 (ofString "ts") (by decide)
    have hcell := (tA k).1
    rw [hck] at hcell
    rw [evalListHOLFinite_eq_toExact] at args
    cases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ts"),.const 16#64])) with
    | none => simp [evalListHOLExact,h1] at args
    | some x1 =>
      have e1 : x1 = .val (.word (T k)) := by
        simp [evalHOLExact,evalListHOLExact,eg,hTs,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,hcell] at h1
        exact h1.2.symm
      subst e1
      simp only [evalListHOLExact,h1] at args
      simp [evalListHOLExact,evalHOLExact,hA,hV] at args
      subst args
      rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
        originalRuntimeCode_journalSet_lookup] at lookup
      simp only [Option.some.injEq,Prod.mk.injEq] at lookup
      obtain ⟨_,rfl,_⟩ := lookup
      exact ⟨⟨A,V,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
        by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
        by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩

#print axioms setAccount_aqg

/-- Contract of `destroy_account(addr)` over the registry (to be discharged; see `htab_del`'s content invariant):
from the registry at heap `H1` every return re-establishes it at the exit heap and keeps every outside word that is
neither in the journal nor in the extra region `Xd`. -/
def DestroyContract (SP0 P0 FM : BitVec 64) (G0 : HolFiniteMapExact MlS (ValueHOL 64)) (w : BitVec 64)
    (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (J C : BitVec 64) (Xd : BitVec 64 → Prop) : Prop :=
  ∀ (H1 : BitVec 64) (M1 : Mem), P0.toNat ≤ H1.toNat →
    AQG (JW SP0 P0 FM G0 J C) w (fun _ => True)
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ Reg n c T Out H1 M ∧
        M = M1 ∧ HeapIs G H1)
      (fun _ _ _ => True)
      (fun _ M' G' => ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧
        ∀ x, Out x → ¬ InJ J C x → ¬ Xd x → M' x = M1 x)
      (sourceFunctionBody Guest.guestFn_destroy_account)

/-- Post-state of `modify_state_commit`: registry at the exit heap, outside words kept unless in the journal or in
the destroy region. -/
def WPostX (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (J C : BitVec 64) (Xd : BitVec 64 → Prop)
    (H0 : BitVec 64) (M0 : Mem) (M' : Mem) (G' : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧
    ∀ x, Out x → ¬ InJ J C x → ¬ Xd x → M' x = M0 x

set_option maxHeartbeats 8000000 in
/-- `modify_state_commit(addr, a)`: `set_account`, then `acct_is_empty` (read-only) and, for an empty account, the
`destroy_account` contract. -/
theorem modifyStateCommit_aqg (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (k : Fin n) (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hck : c k = Ts + 16#64) (J C Nj H0 : BitVec 64)
    (M0 : Mem) (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x)
    (Xd : BitVec 64 → Prop) (hD : DestroyContract SP0 P0 FM G0 w n c T Out J C Xd) :
    AQG (JW SP0 P0 FM G0 J C) w (fun _ => True)
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ Reg n c T Out H0 M ∧ M = M0 ∧
        HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => WPostX n c T Out J C Xd H0 M0 M' G')
      (sourceFunctionBody Guest.guestFn_modify_state_commit) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_modify_state_commit,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  -- set_account(addr, a)
  refine aqg_seq (Q := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ WPostX n c T Out J C Xd H0 M0 M G)
    (aqg_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' G0' L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ M = M0' ∧ G = G0')
      (RRe := fun _ M0' _ _ M' G' => WPost n c T Out J C H0 M0' M' G')
      _ _ _ _ _ originalRuntimeCode_setAccount_lookup (by simp) ?_ ?_ ?_) ?_
  · intro L0 M0' G0' ⟨_,_,reg,_,hH,hn⟩
    refine aqg_conseq (setAccount_aqg n c T Out k Ts hTs hck J C Nj H0 M0' p0 jfit hwJ hwP hOut jsep) ?_
      (fun _ _ _ _ => trivial) (fun _ _ _ h => h.2.2)
    intro L M G ⟨ha,hv,hM,hG⟩
    subst hM hG
    exact ⟨ha,hv,reg,rfl,hH,hn⟩
  · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,⟨V,hV⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA,hV] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_setAccount_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      ⟨V,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨ha,hv,_,hM,_⟩ ⟨H',hH',hle,reg,fr⟩
    subst hM
    exact ⟨ha,hv,H',hH',hle,reg,fun x hx hj _ => fr x hx hj⟩
  -- e = acct_is_empty(a): read-only
  refine aqg_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      WPostX n c T Out J C Xd H0 M0 M G) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_acctIsEmpty_lookup (by simp)
    (fun _ M0' G0' _ => aqg_of_mf acctIsEmpty_mf (by body_check Guest.guestFn_acct_is_empty)
      (by body_check Guest.guestFn_acct_is_empty) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨A,hA⟩,_,wp⟩ ⟨e1,e2⟩ _
    subst e1 e2
    exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,wp⟩
  -- an empty account is destroyed
  refine aqg_seq (Q := fun _ M G => WPostX n c T Out J C Xd H0 M0 M G)
    (aqg_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
      (aqg_conseq aqg_skip (fun _ _ _ h => h.1.2) (fun _ _ _ h => h) (fun _ _ _ h => h)))
    (aqg_return _ (fun _ _ _ _ _ h _ _ => h))
  refine aqg_callSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      M = M0' ∧ G = G0')
    (RRe := fun _ M0' G0' _ M' G' => ∃ H1, HeapIs G0' H1 ∧ ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧
      Reg n c T Out H' M' ∧ ∀ x, Out x → ¬ InJ J C x → ¬ Xd x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_destroyAccount_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨⟨_,H1,hH1,hle,reg,_⟩,_⟩
    refine aqg_conseq (hD H1 M0' (by omega)) ?_ (fun _ _ _ _ => trivial) (fun _ _ _ h => ⟨H1,hH1,h⟩)
    intro L M G ⟨ha,hM,hG⟩
    subst hM hG
    exact ⟨ha,reg,rfl,hH1⟩
  · intro F s values callee rs _ G hG ⟨⟨⟨A,hA⟩,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_destroyAccount_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨_,H1,hH1,hle,_,fr⟩,_⟩ ⟨H1',hH1',H',hH',hle',reg',fr'⟩
    have e : H1' = H1 := by unfold HeapIs at hH1 hH1'; rw [hH1] at hH1'; simpa using hH1'.symm
    subst e
    exact ⟨H',hH',by omega,reg',fun x hx hj hd => (fr' x hx hj hd).trans (fr x hx hj hd)⟩

#print axioms modifyStateCommit_aqg
/-- A call assigning its word result to a local, against a callee spec assuming nothing about the callee's
locals. -/
theorem aqg_callAssignF {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (name function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQG A w (fun _ => False) (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hret : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → (∃ y : BitVec 64, v = .val (.word y)) ∧
      Q (L.update (name,v)) M' H') :
    AQG A w Vn P Q RR (.call (some (some (.local,name),none)) function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      split
      · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (fun _ h => h.elim) H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals (try split)
          all_goals first
            | (obtain ⟨H',hH',rr⟩ := r1 _ rfl
               obtain ⟨⟨y,hy⟩,q⟩ := hret _ _ _ _ _ _ pre rr
               exact ⟨m1,fun _ => a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),
                fun _ => ⟨sl_update sl _ _ (fun _ => ⟨y,hy⟩),H',hH',q⟩,(fun v e => by cases e),by simp,by simp⟩)
            | exact aqg_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

#print axioms aqg_callAssignF

/-- A call assigning its word result to a local, against a callee spec over word parameters. -/
theorem aqg_callAssign {Vn' : MlS → Prop} {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (name function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQG A w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hret : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → (∃ y : BitVec 64, v = .val (.word y)) ∧
      Q (L.update (name,v)) M' H') :
    AQG A w Vn P Q RR (.call (some (some (.local,name),none)) function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      split
      · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (sl_mono (callee_entry_sl function values parameters found returnShape installed allOne found callee foundShape
            lookup') (fun _ _ => trivial)) H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals (try split)
          all_goals first
            | (obtain ⟨H',hH',rr⟩ := r1 _ rfl
               obtain ⟨⟨y,hy⟩,q⟩ := hret _ _ _ _ _ _ pre rr
               exact ⟨m1,fun _ => a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),
                fun _ => ⟨sl_update sl _ _ (fun _ => ⟨y,hy⟩),H',hH',q⟩,(fun v e => by cases e),by simp,by simp⟩)
            | exact aqg_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)


/-- A heap-aware triple holding for every watched word satisfying `Cond` gives a memory frame for all of them. -/
theorem aqmh_family_frame {Vn' : MlS → Prop} {Cond : BitVec 64 → Prop}
    {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop} {RR' : ValueHOL 64 → Mem → BitVec 64 → Prop}
    {p : ProgHOL 64} (h : ∀ x, Cond x → AQMH SP0 P0 FM G0 x Vn' P Q RR' p) (hw : Cond w) (M0 : Mem) :
    AQMH SP0 P0 FM G0 w Vn' (fun L M H => P L M H ∧ M = M0) Q
      (fun v M' H' => RR' v M' H' ∧ ∀ x, Cond x → M' x = M0 x) p := by
  intro F s code dom aw sl H hH ⟨pre,hm⟩
  subst hm
  obtain ⟨m,a,n,r,c,b⟩ := h w hw F s code dom aw sl H hH pre
  refine ⟨m,a,n,fun v e => ?_,c,b⟩
  obtain ⟨H',h1,h2⟩ := r v e
  exact ⟨H',h1,h2,fun x hx => (h x hx F s code dom aw sl H hH pre).1⟩

#print axioms aqmh_family_frame

theorem source_acctCopy_body : sourceFunctionBody Guest.guestFn_acct_copy =
    .decCall (ofString "b") .one (ofString "alloc") [(.const 56)]
      (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "b")),(.var .local (ofString "a")),(.const 56)])
        (.return (.var .local (ofString "b")))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

set_option maxHeartbeats 4000000 in
/-- `acct_copy(a)` from heap pointer `H1`: returns a fresh 56-byte copy at `H1`; memory below `H1` and the journal
counter are kept. -/
theorem acctCopy_aqg (J C Aa H1 N : BitVec 64) (M1 : Mem) (hw1 : w.toNat < H1.toNat) :
    AQG (JW SP0 P0 FM G0 J C) w (fun _ => True)
      (fun L M G => L.lookup (ofString "a") = some (.val (.word Aa)) ∧ M = M1 ∧ HeapIs G H1 ∧
        G.lookup (ofString "journal_n") = some (.val (.word N)))
      (fun _ _ _ => True)
      (fun v M' G' => v = .val (.word H1) ∧ G'.lookup (ofString "journal_n") = some (.val (.word N)) ∧
        ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧ ∀ x, x.toNat < H1.toNat → M' x = M1 x)
      (sourceFunctionBody Guest.guestFn_acct_copy) := by
  rw [source_acctCopy_body]
  refine aqg_decCallSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' _ L M G => G.lookup (ofString "journal_n") = some (.val (.word N)) ∧ ∃ H, HeapIs G H ∧
      (L.lookup (ofString "n") = some (.val (.word 56)) ∧ M = M0' ∧ H = H1))
    (RRe := fun _ M0' _ v M' G' => G'.lookup (ofString "journal_n") = some (.val (.word N)) ∧ ∃ H', HeapIs G' H' ∧
      (M' = M0' ∧ v = .val (.word H1) ∧ H' = allocationEnd H1 56 ∧ P0.toNat ≤ H1.toNat ∧
        H1.toNat + (56 : BitVec 64).toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧ H'.toNat % 8 = 0 ∧ H1.toNat % 8 = 0))
    (Pc := fun L M G => L.lookup (ofString "a") = some (.val (.word Aa)) ∧
      L.lookup (ofString "b") = some (.val (.word H1)) ∧ M = M1 ∧
      G.lookup (ofString "journal_n") = some (.val (.word N)) ∧ H1.toNat % 8 = 0 ∧
      ∃ H2 : BitVec 64, HeapIs G H2 ∧ H1.toNat + 56 ≤ H2.toNat ∧ H2.toNat ≤ 33806089496)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' _ _ => aqg_conseq (aqg_of_aqmh_j (J := J) (C := C) (N := N) originalRuntimeCode_allocation_lookup
      (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) 56 H1 M0'))
      (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h))
    ?_ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ G hG ⟨_,hM,hH,hn⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨hn,H1,hH,by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M G v M' G' ⟨ha,hM,_,_⟩ ⟨hn',H',hH',eM,ev,_,_,c1,fin,_,al⟩ _
    subst eM ev
    exact ⟨by simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using ha,
      by simp [HolFiniteMapExact.lookup_update,FUPDATE],hM,hn',al,H',hH',c1,fin⟩
  refine aqg_seq (Q := fun L M G => L.lookup (ofString "b") = some (.val (.word H1)) ∧
      (∀ x, x.toNat < H1.toNat → M x = M1 x) ∧ G.lookup (ofString "journal_n") = some (.val (.word N)) ∧
      ∃ H2 : BitVec 64, HeapIs G H2 ∧ H1.toNat ≤ H2.toNat)
    (aqg_callSpec (Vn' := fun _ => False)
      (Pe := fun _ M0' G0' L M G => (L.lookup (ofString "dst") = some (.val (.word H1)) ∧
        L.lookup (ofString "src") = some (.val (.word Aa)) ∧ L.lookup (ofString "n") = some (.val (.word 56))) ∧
        M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' _ M' G' => G' = G0' ∧ ∀ x, ¬ MWin H1 (56 : BitVec 64).toNat x → M' x = M0' x)
      _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_)
    (aqg_return _ (fun s v G _ hG ⟨hb,fr,hn,H2,hH2,hle⟩ _ ev => by
      simp [EV,evalHOLExact,hb] at ev
      exact ⟨ev.symm,hn,H2,hH2,hle,fr⟩))
  · intro L0 M0' G0' ⟨_,_,_,_,al,H2,_,c1,fin⟩
    exact aqg_of_window memcpy_body_globals_frame (by body_check Guest.guestFn_memcpy)
      (by body_check Guest.guestFn_memcpy) (MWin H1 (56 : BitVec 64).toNat)
      (fun s _ ⟨hd,hs,hn⟩ x hx => memcpy_body_window s H1 Aa 56 x hd hs hn (by decide) hx)
      (mwin_above hw1 al (by simp; omega)) M0' G0'
  · intro F s values callee rs _ G hG ⟨ha,hb,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,ha,hb] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_memcpy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨_,hb,hM,hn,al,H2,hH2,c1,fin⟩ ⟨eG,fr⟩
    subst eG hM
    refine ⟨hb,fun x hx => fr x (fun hw' => ?_),hn,H2,hH2,by omega⟩
    have := (mwin_ge hw' al (by simp; omega)).1
    omega

#print axioms acctCopy_aqg

/-- The arena predicate holds on normal and returning exits. -/
theorem aqg_withA {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    {p : ProgHOL 64} (h : AQG A w Vn P Q RR p) :
    AQG A w Vn P (fun L M G => Q L M G ∧ A G) (fun v M G => RR v M G ∧ A G) p := by
  intro F s code dom aw sl G hG pre
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl G hG pre
  refine ⟨m,a,fun e => ?_,fun v e => ?_,c,b⟩
  · obtain ⟨sl',G',h1,h2⟩ := n e
    unfold GIs at h1; subst h1
    exact ⟨sl',_,rfl,h2,a (Or.inl e)⟩
  · obtain ⟨G',h1,h2⟩ := r v e
    unfold GIs at h1; subst h1
    exact ⟨_,rfl,h2,a (Or.inr (Or.inr (Or.inr ⟨v,e⟩)))⟩

theorem jw_heap {J C H : BitVec 64} {g : HolFiniteMapExact MlS (ValueHOL 64)} (h : JW SP0 P0 FM G0 J C g)
    (hH : HeapIs g H) : P0.toNat ≤ H.toNat := by
  obtain ⟨⟨_,_,⟨h',hh,lo,_,_⟩,_⟩,_⟩ := h
  unfold HeapIs at hH; rw [hh] at hH
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hH
  subst hH; exact lo

#print axioms aqg_withA

theorem source_incrementNonce_body : sourceFunctionBody Guest.guestFn_increment_nonce =
    .decCall (ofString "a") .one (ofString "get_account") [(.var .local (ofString "addr"))]
      (.seq (.call (some ((some (.local,ofString "a")),none)) (ofString "acct_copy") [(.var .local (ofString "a"))])
      (.seq (.store (.op .add [(.var .local (ofString "a")),(.const 0)])
          (.op .add [(.load .one (.op .add [(.var .local (ofString "a")),(.const 0)])),(.const 1)]))
      (.seq (.call (some (none,none)) (ofString "modify_state_commit") [(.var .local (ofString "addr")),(.var .local (ofString "a"))])
        (.return (.const 0))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Post-state of `increment_nonce`/`set_account_balance`: registry at the exit heap, outside words kept unless in
the journal or in the destroy region. -/
def IncPost (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (J C : BitVec 64) (Xd : BitVec 64 → Prop)
    (M0 : Mem) (M' : Mem) (G' : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ H', HeapIs G' H' ∧ Reg n c T Out H' M' ∧ ∀ x, Out x → ¬ InJ J C x → ¬ Xd x → M' x = M0 x

/-- Outside words lie below the registry's heap pointer. -/
theorem reg_out_lt {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    (h : Reg n c T Out H M) (k : Fin n) (x : BitVec 64) (hx : Out x) : x.toNat < H.toNat := by
  obtain ⟨l,_,_,o⟩ := h
  by_contra cc
  exact o x hx k (Or.inr (Or.inr (by omega)))

set_option maxHeartbeats 16000000 in
/-- `increment_nonce(addr)` over a registry containing the `ts + 8`, `bs + 72` and `ts + 16` tables: `get_account`,
a fresh copy, the nonce store into the copy, and `modify_state_commit` (with the `destroy_account` contract). -/
theorem incrementNonce_aqg (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (kA kB k16 : Fin n)
    (Ts Bs : BitVec 64) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs))) (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72)
    (hck : c k16 = Ts + 16#64) (J C Nj H0 : BitVec 64) (M0 : Mem) (p0 : P0.toNat ≤ H0.toNat)
    (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w) (hwP : w.toNat < P0.toNat) (hOut : Out w)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x)
    (Xd : BitVec 64 → Prop) (hD : DestroyContract SP0 P0 FM G0 w n c T Out J C Xd) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat) :
    AQG (JW SP0 P0 FM G0 J C) w (fun _ => True)
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ Reg n c T Out H0 M ∧
        M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => IncPost n c T Out J C Xd M0 M' G')
      (sourceFunctionBody Guest.guestFn_increment_nonce) := by
  rw [source_incrementNonce_body]
  -- a = get_account(addr)
  refine aqg_decCallSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      M = M0' ∧ G = G0')
    (RRe := fun _ M0' _ _ M' G' => (G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H', HeapIs G' H' ∧
      (Reg n c T Out H' M' ∧ ∀ x, (Out x ∧ WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat) → M' x = M0' x)) ∧
      JW SP0 P0 FM G0 J C G')
    (Pc := fun L M G => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V)))) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1, HeapIs G H1 ∧ P0.toNat ≤ H1.toNat ∧ Reg n c T Out H1 M ∧ ∀ x, Out x → M x = M0 x)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_account_lookup (by simp) ?_ ?_ (fun _ => rfl) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L0 M0' G0' ⟨_,reg,_,hH,hn⟩
    refine aqg_conseq (aqg_withA (aqg_of_aqmh_j (J := J) (C := C) (N := Nj) originalRuntimeCode_account_lookup
      (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (aqmh_family_frame (Cond := fun x => Out x ∧ WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
        (fun x hx => accountReg_aqmh (w := x) n c T kA kB Ts Bs hTs hBs hcA hcB Out hx.1 H0 p0 K Pd NB hK0 hPd0 hNB0
          safe hx.2.1 hx.2.2) ⟨hOut,(hOutSafe w hOut).1,hwP⟩ M0'))) ?_ (fun _ _ _ _ => trivial) (fun _ _ _ h => h)
    intro L M G ⟨ha,hM,hG⟩
    subst hM hG
    exact ⟨hn,H0,hH,⟨ha,rfl,reg⟩,rfl⟩
  · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_account_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨A,hA⟩,_,hM,_⟩ ⟨⟨hn',H1,hH1,reg,fr⟩,jw⟩ ok
    subst hM
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    exact ⟨⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,
      ⟨y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩⟩,hn',H1,hH1,jw_heap jw hH1,reg,
      fun x hx => fr x ⟨hx,hOutSafe x hx⟩⟩
  -- a = acct_copy(a)
  refine aqg_seq (Q := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H1.toNat ≤ H2.toNat ∧ Reg n c T Out H1 M ∧ ∀ x, Out x → M x = M0 x)
    (aqg_callAssign (Vn' := fun _ => True) (Pe := fun _ M0' G0' L M G => (∃ Aa : BitVec 64, L.lookup (ofString "a") = some (.val (.word Aa))) ∧
        M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' v M' G' => ∃ H1, HeapIs G0' H1 ∧ (v = .val (.word H1) ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧ ∀ x, x.toNat < H1.toNat → M' x = M0' x))
      _ _ _ _ _ _ originalRuntimeCode_acctCopy_lookup (by simp) ?_ ?_ ?_) ?_
  · intro L0 M0' G0' ⟨_,hn,H1,hH1,_,reg,_⟩
    have hw1 := reg_out_lt reg kA w hOut
    refine aqg_conseq (P := fun L M G => ∃ Aa, L.lookup (ofString "a") = some (.val (.word Aa)) ∧ M = M0' ∧
        HeapIs G H1 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (aqg_ex (fun Aa => acctCopy_aqg J C Aa H1 Nj M0' hw1)) ?_ (fun _ _ _ _ => trivial) (fun _ _ _ h => ⟨H1,hH1,h⟩)
    intro L M G ⟨⟨Aa,ha⟩,hM,hG⟩
    subst hM hG
    exact ⟨Aa,ha,rfl,hH1,hn⟩
  · intro F s values callee rs _ G hG ⟨⟨_,⟨V,hV⟩⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hV] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_acctCopy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨V,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨A,hA⟩,_⟩,_,H1,hH1,p1,reg,fr⟩ ⟨H1',hH1',ev,hn',H',hH',hle,frc⟩
    have e : H1' = H1 := by unfold HeapIs at hH1 hH1'; rw [hH1] at hH1'; simpa using hH1'.symm
    subst e ev
    have below : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → x.toNat < H1'.toNat := fun x hx => reg_below reg x hx
    refine ⟨⟨_,rfl⟩,⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,hn',
      H1',H',by simp [HolFiniteMapExact.lookup_update,FUPDATE],hH',p1,hle,
      reg_frame reg (fun x hx => frc x (below x hx)),fun x hx => (frc x (reg_out_lt reg kA x hx)).trans (fr x hx)⟩
  -- st a + 0, lds (a + 0) + 1: into the fresh copy
  refine aqg_seq (Q := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H1.toNat ≤ H2.toNat ∧ Reg n c T Out H1 M ∧ ∀ x, Out x → M x = M0 x)
    (aqg_store _ _ (fun s G _ hG ⟨ha,hn,H1,H2,hl,hH2,p1,hle,reg,fr⟩ _ => ?_)
    (fun s x G _ _ _ _ ev => ev_op_word s _ _ x ev)) ?_
  · unfold GIs at hG; subst hG
    have hw1 := reg_out_lt reg kA w hOut
    refine ⟨H1 + 0#64,by simp [EV,evalHOLExact,evalListHOLExact,hl,wordOpHOL,wordOp,valueIsWord,valueWord],
      fun e => by simp at e; subst e; omega,fun y _ => ⟨ha,hn,H1,H2,hl,hH2,p1,hle,
        reg_frame reg (fun x hx => ?_),fun x hx => ?_⟩⟩
    · have : x ≠ H1 + 0#64 := by have := reg_below reg x hx; simp; intro e; subst e; omega
      simp only [if_neg this]
    · have : x ≠ H1 + 0#64 := by have := reg_out_lt reg kA x hx; simp; intro e; subst e; omega
      simp only [if_neg this]; exact fr x hx
  -- modify_state_commit(addr, a)
  refine aqg_seq (Q := fun _ M' G' => IncPost n c T Out J C Xd M0 M' G')
    (aqg_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' G0' L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' _ M' G' => ∃ H2, HeapIs G0' H2 ∧ WPostX n c T Out J C Xd H2 M0' M' G')
      _ _ _ _ _ originalRuntimeCode_modifyStateCommit_lookup (by simp) ?_ ?_ ?_)
    (aqg_return _ (fun _ _ _ _ _ h _ _ => h))
  · intro L0 M0' G0' ⟨_,hn,H1,H2,_,hH2,p1,hle,reg,_⟩
    refine aqg_conseq (modifyStateCommit_aqg n c T Out k16 Ts hTs hck J C Nj H2 M0' (by omega) jfit hwJ hwP hOut
      jsep Xd hD) ?_ (fun _ _ _ _ => trivial) (fun _ _ _ h => ⟨H2,hH2,h⟩)
    intro L M G ⟨ha,hv,hM,hG⟩
    subst hM hG
    exact ⟨ha,hv,reg_mono reg hle,rfl,hH2,hn⟩
  · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,_,H1,_,hl,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA,hl] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_modifyStateCommit_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      ⟨H1,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨_,_,H1,H2,_,hH2,_,_,_,fr⟩ ⟨H2',hH2',H',hH',_,reg',fr'⟩
    exact ⟨H',hH',reg',fun x hx hj hd => (fr' x hx hj hd).trans (fr x hx)⟩

#print axioms incrementNonce_aqg

/-- A four-word struct store: the normal postcondition holds for any memory differing only at the four words. -/
theorem aqg_store4 {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) G, A s.globals → GIs s.globals G → P s.locals s.memory G →
      SL Vn s.locals → ∃ a b0 b1 b2 b3 : BitVec 64, EV s d = some (.val (.word a)) ∧
        EV s v = some (.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)]) ∧
        w ≠ a ∧ w ≠ a + 8#64 ∧ w ≠ a + 16#64 ∧ w ≠ a + 24#64 ∧
        ∀ M' : Mem, (∀ x, x ≠ a → x ≠ a + 8#64 → x ≠ a + 16#64 → x ≠ a + 24#64 → M' x = s.memory x) →
          Q s.locals M' G) :
    AQG A w Vn P Q RR (.store d v) := by
  intro F s code dom aw sl G hG pre
  obtain ⟨a,b0,b1,b2,b3,ha,hv,n0,n8,n16,n24,hq⟩ := hd s G aw hG pre sl
  have fr : ∀ x, x ≠ a → x ≠ a + 8#64 → x ≠ a + 16#64 → x ≠ a + 24#64 →
      (evaluateHOLFiniteState s (.store d v)).2.memory x = s.memory x :=
    fun x e0 e8 e16 e24 => evaluate_fourWordStore_memory_frame s d v a b0 b1 b2 b3 x ha hv e0 e8 e16 e24
  obtain ⟨res,loc,glob⟩ := store_ctl s d v
  refine ⟨fr w n0 n8 n16 n24,fun _ => by rw [glob]; exact aw,fun _ => ⟨by rw [loc]; exact sl,G,
    by unfold GIs; rw [glob]; exact hG,by rw [loc]; exact hq _ fr⟩,?_,?_,?_⟩ <;>
    rcases res with h | h <;> rw [h] <;> simp

#print axioms aqg_store4

theorem source_setAccountBalance_body : sourceFunctionBody Guest.guestFn_set_account_balance =
    .decCall (ofString "a") .one (ofString "get_account") [(.var .local (ofString "addr"))]
      (.seq (.call (some ((some (.local,ofString "a")),none)) (ofString "acct_copy") [(.var .local (ofString "a"))])
      (.seq (.store (.op .add [(.var .local (ofString "a")),(.const 8)]) (.var .local (ofString "amount")))
      (.seq (.call (some (none,none)) (ofString "modify_state_commit") [(.var .local (ofString "addr")),(.var .local (ofString "a"))])
        (.return (.const 0))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The four-word balance argument. -/
def AmtL (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ b0 b1 b2 b3 : BitVec 64,
    L.lookup (ofString "amount") = some (.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)])

theorem amtL_update {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : AmtL L) (v : ValueHOL 64) : AmtL (L.update (ofString "a",v)) := by
  obtain ⟨b0,b1,b2,b3,hb⟩ := h
  exact ⟨b0,b1,b2,b3,by simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using hb⟩

theorem jw_heap_hi {J C H : BitVec 64} {g : HolFiniteMapExact MlS (ValueHOL 64)} (h : JW SP0 P0 FM G0 J C g)
    (hH : HeapIs g H) : H.toNat ≤ 33806089496 := by
  obtain ⟨⟨_,_,⟨h',hh,_,hi,_⟩,_⟩,_⟩ := h
  unfold HeapIs at hH; rw [hh] at hH
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hH
  subst hH; exact hi
set_option maxHeartbeats 16000000 in
/-- `set_account_balance(addr, amount)` over a registry containing the `ts + 8`, `bs + 72` and `ts + 16` tables:
`get_account`, a fresh copy, the four-word balance store into the copy, and `modify_state_commit` (with the
`destroy_account` contract). -/
theorem setAccountBalance_aqg (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (kA kB k16 : Fin n)
    (Ts Bs : BitVec 64) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs))) (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72)
    (hck : c k16 = Ts + 16#64) (J C Nj H0 : BitVec 64) (M0 : Mem) (p0 : P0.toNat ≤ H0.toNat)
    (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w) (hwP : w.toNat < P0.toNat) (hOut : Out w)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x)
    (Xd : BitVec 64 → Prop) (hD : DestroyContract SP0 P0 FM G0 w n c T Out J C Xd) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat) :
    AQG (JW SP0 P0 FM G0 J C) w (fun x => x ≠ ofString "amount")
      (fun L M G => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ AmtL L) ∧
        Reg n c T Out H0 M ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => IncPost n c T Out J C Xd M0 M' G')
      (sourceFunctionBody Guest.guestFn_set_account_balance) := by
  rw [source_setAccountBalance_body]
  -- a = get_account(addr)
  refine aqg_decCallSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      M = M0' ∧ G = G0')
    (RRe := fun _ M0' _ _ M' G' => (G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H', HeapIs G' H' ∧
      (Reg n c T Out H' M' ∧ ∀ x, (Out x ∧ WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat) → M' x = M0' x)) ∧
      JW SP0 P0 FM G0 J C G')
    (Pc := fun L M G => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ AmtL L) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1, HeapIs G H1 ∧ P0.toNat ≤ H1.toNat ∧ Reg n c T Out H1 M ∧ ∀ x, Out x → M x = M0 x)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_account_lookup (by simp) ?_ ?_ (fun _ => rfl) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L0 M0' G0' ⟨_,reg,_,hH,hn⟩
    refine aqg_conseq (aqg_withA (aqg_of_aqmh_j (J := J) (C := C) (N := Nj) originalRuntimeCode_account_lookup
      (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (aqmh_family_frame (Cond := fun x => Out x ∧ WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
        (fun x hx => accountReg_aqmh (w := x) n c T kA kB Ts Bs hTs hBs hcA hcB Out hx.1 H0 p0 K Pd NB hK0 hPd0 hNB0
          safe hx.2.1 hx.2.2) ⟨hOut,(hOutSafe w hOut).1,hwP⟩ M0'))) ?_ (fun _ _ _ _ => trivial) (fun _ _ _ h => h)
    intro L M G ⟨ha,hM,hG⟩
    subst hM hG
    exact ⟨hn,H0,hH,⟨ha,rfl,reg⟩,rfl⟩
  · intro F s values callee rs _ G hG ⟨⟨⟨A,hA⟩,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_account_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨A,hA⟩,am⟩,_,hM,_⟩ ⟨⟨hn',H1,hH1,reg,fr⟩,jw⟩ ok
    subst hM
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    exact ⟨⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,
      ⟨y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,amtL_update am _⟩,hn',H1,hH1,jw_heap jw hH1,reg,
      fun x hx => fr x ⟨hx,hOutSafe x hx⟩⟩
  -- a = acct_copy(a)
  refine aqg_seq (Q := fun L M G => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ AmtL L) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H1.toNat ≤ H2.toNat ∧ Reg n c T Out H1 M ∧ ∀ x, Out x → M x = M0 x)
    (aqg_callAssign (Vn' := fun _ => True) (Pe := fun _ M0' G0' L M G => (∃ Aa : BitVec 64, L.lookup (ofString "a") = some (.val (.word Aa))) ∧
        M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' v M' G' => ∃ H1, HeapIs G0' H1 ∧ (v = .val (.word H1) ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧ ∀ x, x.toNat < H1.toNat → M' x = M0' x))
      _ _ _ _ _ _ originalRuntimeCode_acctCopy_lookup (by simp) ?_ ?_ ?_) ?_
  · intro L0 M0' G0' ⟨_,hn,H1,hH1,_,reg,_⟩
    have hw1 := reg_out_lt reg kA w hOut
    refine aqg_conseq (P := fun L M G => ∃ Aa, L.lookup (ofString "a") = some (.val (.word Aa)) ∧ M = M0' ∧
        HeapIs G H1 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (aqg_ex (fun Aa => acctCopy_aqg J C Aa H1 Nj M0' hw1)) ?_ (fun _ _ _ _ => trivial) (fun _ _ _ h => ⟨H1,hH1,h⟩)
    intro L M G ⟨⟨Aa,ha⟩,hM,hG⟩
    subst hM hG
    exact ⟨Aa,ha,rfl,hH1,hn⟩
  · intro F s values callee rs _ G hG ⟨⟨_,⟨V,hV⟩,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hV] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_acctCopy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨V,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨A,hA⟩,_,am⟩,_,H1,hH1,p1,reg,fr⟩ ⟨H1',hH1',ev,hn',H',hH',hle,frc⟩
    have e : H1' = H1 := by unfold HeapIs at hH1 hH1'; rw [hH1] at hH1'; simpa using hH1'.symm
    subst e ev
    have below : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → x.toNat < H1'.toNat := fun x hx => reg_below reg x hx
    refine ⟨⟨_,rfl⟩,⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,amtL_update am _⟩,hn',
      H1',H',by simp [HolFiniteMapExact.lookup_update,FUPDATE],hH',p1,hle,
      reg_frame reg (fun x hx => frc x (below x hx)),fun x hx => (frc x (reg_out_lt reg kA x hx)).trans (fr x hx)⟩
  -- st a + 8, amount: four words into the fresh copy
  refine aqg_seq (Q := fun L M G => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ AmtL L) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H1.toNat ≤ H2.toNat ∧ Reg n c T Out H1 M ∧ ∀ x, Out x → M x = M0 x)
    (aqg_store4 _ _ (fun s G aw hG ⟨⟨ha,⟨b0,b1,b2,b3,hb⟩⟩,hn,H1,H2,hl,hH2,p1,hle,reg,fr⟩ _ => ?_)) ?_
  · unfold GIs at hG; subst hG
    have hw1 := reg_out_lt reg kA w hOut
    have hi := jw_heap_hi aw hH2
    have e : ∀ k : BitVec 64, k.toNat < 40 → (H1 + 8#64 + k).toNat = H1.toNat + 8 + k.toNat := fun k hk => by
      rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega),
        BitVec.toNat_add_of_lt (by simp; omega)]; simp
    have e0 : (H1 + 8#64).toNat = H1.toNat + 8 := by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp
    have low : ∀ x, x.toNat < H1.toNat → x ≠ H1 + 8#64 ∧ x ≠ H1 + 8#64 + 8#64 ∧ x ≠ H1 + 8#64 + 16#64 ∧
        x ≠ H1 + 8#64 + 24#64 := fun x hx =>
      ⟨fun h => by subst h; rw [e0] at hx; omega,fun h => by subst h; rw [e _ (by decide)] at hx; simp at hx; omega,
        fun h => by subst h; rw [e _ (by decide)] at hx; simp at hx; omega,
        fun h => by subst h; rw [e _ (by decide)] at hx; simp at hx; omega⟩
    obtain ⟨l0,l8,l16,l24⟩ := low w hw1
    refine ⟨H1 + 8#64,b0,b1,b2,b3,
      by simp [EV,evalHOLExact,evalListHOLExact,hl,wordOpHOL,wordOp,valueIsWord,valueWord],
      by simp [EV,evalHOLExact,hb],l0,l8,l16,l24,fun M' hM' => ⟨⟨ha,b0,b1,b2,b3,hb⟩,hn,H1,H2,hl,hH2,p1,hle,
        reg_frame reg (fun x hx => ?_),fun x hx => ?_⟩⟩
    · obtain ⟨a0,a8,a16,a24⟩ := low x (reg_below reg x hx)
      exact hM' x a0 a8 a16 a24
    · obtain ⟨a0,a8,a16,a24⟩ := low x (reg_out_lt reg kA x hx)
      exact (hM' x a0 a8 a16 a24).trans (fr x hx)
  -- modify_state_commit(addr, a)
  refine aqg_seq (Q := fun _ M' G' => IncPost n c T Out J C Xd M0 M' G')
    (aqg_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' G0' L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' _ M' G' => ∃ H2, HeapIs G0' H2 ∧ WPostX n c T Out J C Xd H2 M0' M' G')
      _ _ _ _ _ originalRuntimeCode_modifyStateCommit_lookup (by simp) ?_ ?_ ?_)
    (aqg_return _ (fun _ _ _ _ _ h _ _ => h))
  · intro L0 M0' G0' ⟨_,hn,H1,H2,_,hH2,p1,hle,reg,_⟩
    refine aqg_conseq (modifyStateCommit_aqg n c T Out k16 Ts hTs hck J C Nj H2 M0' (by omega) jfit hwJ hwP hOut
      jsep Xd hD) ?_ (fun _ _ _ _ => trivial) (fun _ _ _ h => ⟨H2,hH2,h⟩)
    intro L M G ⟨ha,hv,hM,hG⟩
    subst hM hG
    exact ⟨ha,hv,reg_mono reg hle,rfl,hH2,hn⟩
  · intro F s values callee rs _ G hG ⟨⟨⟨A,hA⟩,_⟩,_,H1,_,hl,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA,hl] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_modifyStateCommit_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      ⟨H1,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨_,_,H1,H2,_,hH2,_,_,_,fr⟩ ⟨H2',hH2',H',hH',_,reg',fr'⟩
    exact ⟨H',hH',reg',fun x hx hj hd => (fr' x hx hj hd).trans (fr x hx)⟩

#print axioms aqg_callAssign
#print axioms setAccountBalance_aqg
end InitECandidate.Runtime
