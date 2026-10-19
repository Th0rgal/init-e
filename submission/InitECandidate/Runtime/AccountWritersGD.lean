import InitECandidate.Runtime.ModifyStateCommitGD
/-!
Account writers over the content-carrying registry `RegT`. `aqmh_side_frame` combines a main heap-aware triple with
per-word triples at a higher arena bound; `aqmh_heap_ge` records that the exit heap is at least the raised bound;
`reg_sub2` extracts a two-table sub-registry. `accountRegT_aqmh`: the original `get_account` additionally keeps the
outer storage table's header and arrays (off the workspace) and the outside words, with the exit heap above the entry
heap. `incrementNonceT_aqgd`: the original `increment_nonce` (get_account, acct_copy, nonce store, the original
modify_state_commit) re-establishes `RegT` without any destroy contract.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : GA} {Vn : MlS → Prop}

/-- Side frames: a main triple for `w` at arena `P0`, together with triples for every word of `S` at the higher arena
bound `Q0` (at most the entry heap), gives the main triple with the words of `S` kept on a return. -/
theorem aqmh_side_frame {Q0 : BitVec 64} {S : BitVec 64 → Prop}
    {P Q P' Q' : GA → Mem → BitVec 64 → Prop} {RR RR' : ValueHOL 64 → Mem → BitVec 64 → Prop} {p : ProgHOL 64}
    (M0 : Mem) (hmain : AQMH SP0 P0 FM G0 w Vn P Q RR p)
    (hS : ∀ x, S x → AQMH SP0 Q0 FM G0 x Vn P' Q' RR' p)
    (hP : ∀ L M H, P L M H → M = M0 → Q0.toNat ≤ H.toNat ∧ P' L M H) :
    AQMH SP0 P0 FM G0 w Vn (fun L M H => P L M H ∧ M = M0) Q
      (fun v M' H' => RR v M' H' ∧ ∀ x, S x → M' x = M0 x) p := by
  intro F s code dom aw sl H hH ⟨pre,hm⟩
  have hq := hP _ _ _ pre hm
  subst hm
  obtain ⟨m,a,n,r,c,b⟩ := hmain F s code dom aw sl H hH pre
  have awQ : AW SP0 Q0 FM G0 s.globals := by
    obtain ⟨hf,hs,⟨h',hh,_,hi,al⟩,st⟩ := aw
    have e : h' = H := by unfold HeapIs at hH; rw [hh] at hH; simpa using hH
    subst e
    exact ⟨hf,hs,⟨h',hh,hq.1,hi,al⟩,st⟩
  refine ⟨m,a,n,fun v e => ?_,c,b⟩
  obtain ⟨H',h1,h2⟩ := r v e
  exact ⟨H',h1,h2,fun x hx => (hS x hx F s code dom awQ sl H hH hq.2).1⟩

#print axioms aqmh_side_frame


/-- Lowering the arena bound from `Q` to `P0` while recording on a return that the exit heap is at least `Q`. -/
theorem aqmh_heap_ge {Q : BitVec 64} {P Qp : GA → Mem → BitVec 64 → Prop} {RR : ValueHOL 64 → Mem → BitVec 64 → Prop}
    {p : ProgHOL 64} (h : AQMH SP0 Q FM G0 w Vn P Qp RR p) (le : P0.toNat ≤ Q.toNat) :
    AQMH SP0 P0 FM G0 w Vn (fun L M H => Q.toNat ≤ H.toNat ∧ P L M H) Qp
      (fun v M H' => RR v M H' ∧ Q.toNat ≤ H'.toNat) p := by
  intro F s code dom aw sl H hH ⟨hq,pre⟩
  have awQ : AW SP0 Q FM G0 s.globals := by
    obtain ⟨hf,hs,⟨h',hh,_,hi,al⟩,st⟩ := aw
    have e : h' = H := by unfold HeapIs at hH; rw [hh] at hH; simpa using hH
    subst e
    exact ⟨hf,hs,⟨h',hh,hq,hi,al⟩,st⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom awQ sl H hH pre
  refine ⟨m,fun cont => (aw_lower (a cont) le).1,n,fun v e => ?_,c,b⟩
  obtain ⟨H',h1,h2⟩ := r v e
  obtain ⟨_,_,⟨h',hh,hge,_,_⟩,_⟩ := a (Or.inr (Or.inr (Or.inr ⟨v,e⟩)))
  have e' : h' = H' := by unfold HeapIs at h1; rw [hh] at h1; simpa using h1
  subst e'
  exact ⟨h',h1,h2,hge⟩

#print axioms aqmh_heap_ge

/-- Two entries of a family indexed by `Fin n`. -/
def sub2 {α : Type} {n : Nat} (f : Fin n → α) (a b : Fin n) : Fin 2 → α := fun i => if i.val = 0 then f a else f b

theorem sub2_zero {α : Type} {n : Nat} (f : Fin n → α) (a b : Fin n) : sub2 f a b 0 = f a := rfl
theorem sub2_one {α : Type} {n : Nat} (f : Fin n → α) (a b : Fin n) : sub2 f a b 1 = f b := rfl

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨_ | _ | k,h⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

/-- The two-table sub-registry `{a, b}` of a registry, with any outside set avoiding both footprints. -/
theorem reg_sub2 {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    (l : Fin n → TLay) (pure : RegPure n c T Out H l) (mem : RegMem n c T l M) (a b : Fin n) (hab : a ≠ b)
    (S : BitVec 64 → Prop) (hS : ∀ x, S x → ¬ (l a).canon (T a) H x ∧ ¬ (l b).canon (T b) H x) :
    Reg 2 (sub2 c a b) (sub2 T a b) S H M := by
  have tA := reg_of pure mem
  refine ⟨sub2 l a b,fun i => ?_,fun i j ne => ?_,fun x hx i => ?_⟩
  · rcases fin2_cases i with rfl | rfl
    · exact tA a
    · exact tA b
  · rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl
    · exact absurd rfl ne
    · exact pure.2.1 a b hab
    · exact pure.2.1 b a (Ne.symm hab)
    · exact absurd rfl ne
  · rcases fin2_cases i with rfl | rfl
    · exact (hS x hx).1
    · exact (hS x hx).2

#print axioms reg_sub2

/-- Words kept by `get_account` besides the registry: the outer storage table's header and arrays and the outside
words, all off the workspace. -/
def GaKeep (SP0 P0 FM K Pd NB : BitVec 64) (Out : BitVec 64 → Prop) (To : BitVec 64) (lo : TLay) (x : BitVec 64) :
    Prop :=
  (InTabF To lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x ∧ WsSafe SP0 FM K Pd NB x) ∨
    (Out x ∧ WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)

set_option maxHeartbeats 8000000 in
/-- `get_account(addr)` over a registry with fixed entry layouts: as `accountReg_aqmh`, and a return also keeps the
header and arrays of a table `ko` other than the two read tables (when off the workspace) and the outside words. -/
theorem accountRegT_aqmh (n : Nat) (c T : Fin n → BitVec 64) (kA kB ko : Fin n) (hAB : kA ≠ kB) (hAo : kA ≠ ko)
    (hBo : kB ≠ ko) (Ts Bs : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (Out : BitVec 64 → Prop) (hOut : Out w)
    (H0 : BitVec 64) (p0 : P0.toNat ≤ H0.toNat) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (ws : WsSafe SP0 FM K Pd NB w) (hp : w.toNat < P0.toNat)
    (l : Fin n → TLay) (pure : RegPure n c T Out H0 l) (M0 : Mem) (mem : RegMem n c T l M0)
    (ab : ∀ x, (l ko).arr x → x.toNat < H0.toNat) :
    AQMH SP0 P0 FM G0 w (fun _ => True)
      (fun L M H => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0 ∧
        Reg n c T Out H0 M) ∧ M = M0)
      (fun _ _ _ => True)
      (fun _ M' H' => (Reg n c T Out H' M' ∧ H0.toNat ≤ H'.toNat) ∧
        ∀ x, GaKeep SP0 P0 FM K Pd NB Out (T ko) (l ko) x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_get_account) := by
  let S2 : BitVec 64 → Prop := fun x =>
    InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x ∧ WsSafe SP0 FM K Pd NB x
  have below : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
      x.toNat < H0.toNat := by
    intro x hx
    rcases hx with hh | ha
    · have := (pure.1 ko).1.hdrP; omega
    · exact ab x ha
  have hS2 : ∀ x, S2 x → ¬ (l kA).canon (T kA) H0 x ∧ ¬ (l kB).canon (T kB) H0 x := by
    intro x ⟨hx,_⟩
    have inj : x = c ko ∨ HdrR (T ko) x ∨ (l ko).arr x := by
      rcases hx with hh | ha
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr ha)
    exact ⟨pure.2.1 kA ko hAo x inj,pure.2.1 kB ko hBo x inj⟩
  have safe2 : ∀ x, (∃ i, x = sub2 c kA kB i ∨ HdrR (sub2 T kA kB i) x) → WsSafe SP0 FM K Pd NB x := by
    intro x ⟨i,hi⟩
    rcases fin2_cases i with rfl | rfl
    · exact safe x ⟨kA,hi⟩
    · exact safe x ⟨kB,hi⟩
  refine aqmh_side_frame (Q0 := H0)
    (P' := fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0 ∧
      Reg n c T Out H0 M ∧ Reg 2 (sub2 c kA kB) (sub2 T kA kB) S2 H0 M)
    (Q' := fun _ _ _ => True) (RR' := fun _ _ _ => True) M0
    (aqmh_conseq (aqmh_heap_ge (accountReg_aqmh (P0 := H0) n c T kA kB Ts Bs hTs hBs hcA hcB Out hOut H0
      (le_refl _) K Pd NB hK0 hPd0 hNB0 safe ws (by omega)) p0) (fun _ _ _ ⟨ha,hH,reg⟩ => ⟨by rw [hH],ha,hH,reg⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h))
    (fun x hx => ?_) (fun L M H ⟨ha,hH,reg⟩ hM => ⟨by rw [hH],ha,hH,reg,
      reg_sub2 l pure (by rw [hM]; exact mem) kA kB hAB S2 hS2⟩)
  rcases hx with hx | ⟨ho,hs,hlt⟩
  · exact aqmh_conseq (accountReg_aqmh (P0 := H0) (w := x) 2 (sub2 c kA kB) (sub2 T kA kB) 0 1 Ts Bs hTs hBs
      ((sub2_zero c kA kB).trans hcA) ((sub2_one c kA kB).trans hcB) S2 hx H0 (le_refl _) K Pd NB hK0 hPd0 hNB0
      safe2 hx.2 (below x hx.1)) (fun _ _ _ ⟨ha,hH,_,r2⟩ => ⟨ha,hH,r2⟩) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
  · exact aqmh_conseq (accountReg_aqmh (P0 := H0) (w := x) n c T kA kB Ts Bs hTs hBs hcA hcB Out ho H0 (le_refl _)
      K Pd NB hK0 hPd0 hNB0 safe hs (by omega)) (fun _ _ _ ⟨ha,hH,r,_⟩ => ⟨ha,hH,r⟩) (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)

#print axioms accountRegT_aqmh
variable {D : BitVec 64 → Prop} {B : Bool}

/-- Writes at or above the registry's heap pointer keep the registry with content. -/
theorem regT_keep_below {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M M' : Mem}
    {ko : Fin n} (h : RegT n c T Out H M D B ko) (keep : ∀ x, x.toNat < H.toNat → M' x = M x) :
    RegT n c T Out H M' D B ko := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h
  have fitT : ∀ i, (T i).toNat + 72 < 2 ^ 64 := fun i => by have := (pure.1 i).1.eEnd; omega
  refine ⟨l,pure,regMem_frame mem fitT (fun x hx => keep x (regPure_below pure x hx)),
    tc.frame (pure.1 ko).1.cnt.le (fun x hx => keep x ?_),ab⟩
  rcases hx with hh | ha
  · have := (pure.1 ko).1.hdrP; omega
  · exact ab x ha

#print axioms regT_keep_below

section inc
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 : Fin n}
  {Ts Bs SKB J C Nj H0 : BitVec 64} {M0 : Mem}

set_option maxHeartbeats 32000000 in
/-- The original `increment_nonce(addr)` over the content-carrying registry: `get_account` (the account read tables
`kA`, `kB` at `ts + 8`, `bs + 72`), a fresh copy, the nonce store into the copy, and the original
`modify_state_commit` (account table `k16` at `ts + 16`, no destroy contract). -/
theorem incrementNonceT_aqgd (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ lo : TLay, lo.hdr M0 (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => True)
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => DAPost n c T Out ko D B J C SKB H0 M0 M' G')
      (sourceFunctionBody Guest.guestFn_increment_nonce) := by
  rw [source_incrementNonce_body]
  refine aqgd_conseq (P := fun L M G => ∃ l : Fin n → TLay,
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ RegPure n c T Out H0 l ∧
      RegMem n c T l M ∧ TCont D B M (T ko) (l ko) ∧ (∀ x, (l ko).arr x → x.toNat < H0.toNat) ∧ M = M0 ∧
      HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (aqgd_ex (fun l => ?_)) (fun L M G ⟨ha,⟨l,pure,mem,tc,ab⟩,hM,hH,hn⟩ => ⟨l,ha,pure,mem,tc,ab,hM,hH,hn⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  -- a = get_account(addr)
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      M = M0' ∧ G = G0')
    (RRe := fun _ M0' _ _ M' G' => (G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H', HeapIs G' H' ∧
      ((Reg n c T Out H' M' ∧ H0.toNat ≤ H'.toNat) ∧
        ∀ x, GaKeep SP0 P0 FM K Pd NB Out (T ko) (l ko) x → M' x = M0' x)) ∧ JW SP0 P0 FM G0 J C G')
    (Pc := fun L M G => ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V)))) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1, HeapIs G H1 ∧ P0.toNat ≤ H1.toNat ∧ H0.toNat ≤ H1.toNat ∧ RegT n c T Out H1 M D B ko ∧
        ∀ x, Out x → M x = M0 x)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_account_lookup (by simp) ?_ ?_ (fun _ => rfl) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L0 M0' G0' ⟨_,pure,mem,_,ab,_,hH,hn⟩
    refine aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_withA (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_account_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (accountRegT_aqmh n c T kA kB ko hAB hAo hBo Ts Bs hTs hBs hcA hcB Out hOut H0 p0 K Pd NB hK0 hPd0 hNB0
        safe (hOutSafe w hOut).1 hwP l pure M0' mem ab))))
      (keepsSkBuf_of_installed originalRuntimeCode_account_lookup (by decide))) ?_ (fun _ _ _ _ => trivial)
      (fun _ _ _ h => h)
    intro L M G ⟨ha,hM,hG⟩
    subst hM hG
    exact ⟨hn,H0,hH,⟨ha,rfl,l,reg_of pure mem,pure.2.1,pure.2.2⟩,rfl⟩
  · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_account_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨A,hA⟩,pure,mem,tc,ab,hM,_⟩ ⟨⟨hn',H1,hH1,⟨reg,hle⟩,fr⟩,jw⟩ ok
    subst hM
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    have keepT : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
        M' x = M x := fun x hx => fr x (Or.inl ⟨hx,hkoWs (l ko) (mem ko).2 x hx⟩)
    exact ⟨⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,
      ⟨y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩⟩,hn',H1,hH1,jw_heap jw hH1,hle,
      regT_of_reg l pure tc ab reg hle keepT,fun x hx => fr x (Or.inr ⟨hx,hOutSafe x hx⟩)⟩
  -- a = acct_copy(a)
  refine aqgd_seq (Q := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H0.toNat ≤ H1.toNat ∧ H1.toNat ≤ H2.toNat ∧ RegT n c T Out H1 M D B ko ∧ ∀ x, Out x → M x = M0 x)
    (aqgd_jws (aqgd_of_aqg (aqg_callAssign (Vn' := fun _ => True)
      (Pe := fun _ M0' G0' L M G => (∃ Aa : BitVec 64, L.lookup (ofString "a") = some (.val (.word Aa))) ∧
        M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' v M' G' => ∃ H1, HeapIs G0' H1 ∧ (v = .val (.word H1) ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧ ∀ x, x.toNat < H1.toNat → M' x = M0' x))
      _ _ _ _ _ _ originalRuntimeCode_acctCopy_lookup (by simp) ?_ ?_ ?_)) (by decide)) ?_
  · intro L0 M0' G0' ⟨_,hn,H1,hH1,_,_,reg,_⟩
    have hw1 : w.toNat < H1.toNat := by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 w hOut ko (Or.inr (Or.inr (by omega)))
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
  · intro L M G v M' G' ⟨⟨⟨A,hA⟩,_⟩,_,H1,hH1,p1,h01,reg,fr⟩ ⟨H1',hH1',ev,hn',H',hH',hle,frc⟩
    have e : H1' = H1 := by unfold HeapIs at hH1 hH1'; rw [hH1] at hH1'; simpa using hH1'.symm
    subst e ev
    have ltOut : ∀ x, Out x → x.toNat < H1'.toNat := fun x hx => by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 x hx ko (Or.inr (Or.inr (by omega)))
    refine ⟨⟨_,rfl⟩,⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,hn',
      H1',H',by simp [HolFiniteMapExact.lookup_update,FUPDATE],hH',p1,h01,hle,
      regT_keep_below reg (fun x hx => frc x hx),fun x hx => (frc x (ltOut x hx)).trans (fr x hx)⟩
  -- st a + 0, lds (a + 0) + 1: into the fresh copy
  refine aqgd_seq (Q := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H1 H2, L.lookup (ofString "a") = some (.val (.word H1)) ∧ HeapIs G H2 ∧ P0.toNat ≤ H1.toNat ∧
        H0.toNat ≤ H1.toNat ∧ H1.toNat ≤ H2.toNat ∧ RegT n c T Out H1 M D B ko ∧ ∀ x, Out x → M x = M0 x)
    (aqgd_store _ _ (fun s G _ hG ⟨ha,hn,H1,H2,hl,hH2,p1,h01,hle,reg,fr⟩ _ => ?_)
    (fun s x G _ _ _ _ ev => ev_op_word s _ _ x ev)) ?_
  · unfold GIs at hG; subst hG
    have hw1 : w.toNat < H1.toNat := by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 w hOut ko (Or.inr (Or.inr (by omega)))
    have ltOut : ∀ x, Out x → x.toNat < H1.toNat := fun x hx => by
      obtain ⟨l',pure',_⟩ := reg
      by_contra cc; exact pure'.2.2 x hx ko (Or.inr (Or.inr (by omega)))
    refine ⟨H1 + 0#64,by simp [EV,evalHOLExact,evalListHOLExact,hl,wordOpHOL,wordOp,valueIsWord,valueWord],
      fun e => by simp at e; subst e; omega,fun y _ => ⟨ha,hn,H1,H2,hl,hH2,p1,h01,hle,
        regT_keep_below reg (fun x hx => ?_),fun x hx => ?_⟩⟩
    · have : x ≠ H1 + 0#64 := by simp; intro e; subst e; omega
      simp only [if_neg this]
    · have : x ≠ H1 + 0#64 := by have := ltOut x hx; simp; intro e; subst e; omega
      simp only [if_neg this]; exact fr x hx
  -- modify_state_commit(addr, a)
  refine aqgd_seq (Q := fun _ M' G' => DAPost n c T Out ko D B J C SKB H0 M0 M' G')
    (aqgd_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' _ L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧
        (∃ H2, RegT n c T Out H2 M D B ko ∧ HeapIs G H2 ∧ H0.toNat ≤ H2.toNat) ∧ M = M0' ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (RRe := fun _ M0' _ _ M' G' => DAPost n c T Out ko D B J C SKB H0 M0' M' G')
      _ _ _ _ _ originalRuntimeCode_modifyStateCommit_lookup (by simp) ?_ ?_ ?_)
    (aqgd_return _ (fun _ _ _ _ _ h _ _ => h))
  · intro L0 M0' G0' _
    refine aqgd_conseq (P := fun L M G => ∃ H2 : BitVec 64, H0.toNat ≤ H2.toNat ∧
        ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧
        RegT n c T Out H2 M D B ko ∧ M = M0' ∧ HeapIs G H2 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))))
      (aqgd_ex (fun H2 => aqgd_conseq (P := fun L M G =>
          ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
          (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧
          RegT n c T Out H2 M D B ko ∧ M = M0' ∧ HeapIs G H2 ∧
          G.lookup (ofString "journal_n") = some (.val (.word Nj))) ∧ H0.toNat ≤ H2.toNat)
        (aqgd_purePre (fun h02 => aqgd_conseq (modifyStateCommitT_aqgd (H0 := H2) (Nj := Nj) (M0 := M0') ne ne16
          hTs hco hcd hc16 (by omega) jfit hwJ hwP hOut hwS hJO hSO jsep) (fun _ _ _ h => h) (fun _ _ _ h => h)
          (fun _ _ _ ⟨H',hH',hle',r,hn,fr⟩ => ⟨H',hH',by omega,r,hn,fr⟩)))
        (fun L M G ⟨h02,rest⟩ => ⟨rest,h02⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)))
      (fun L M G ⟨ha,hv,⟨H2,reg,hH2,h02⟩,hM,hn⟩ => ⟨H2,h02,ha,hv,reg,hM,hH2,hn⟩) (fun _ _ _ h => h)
      (fun _ _ _ h => h)
  · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,hn,H1,H2,hl,hH2,_,h01,hle,reg,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA,hl] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_modifyStateCommit_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      ⟨H1,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      ⟨H2,regT_mono reg hle,hH2,by omega⟩,rfl,hn⟩
  · intro L M G v M' G' ⟨_,_,H1,H2,_,_,_,_,_,_,fr⟩ ⟨H',hH',hle',reg',hn',fr'⟩
    exact ⟨H',hH',hle',reg',hn',fun x hx hj hs => (fr' x hx hj hs).trans (fr x hx)⟩

#print axioms incrementNonceT_aqgd
end inc
end InitECandidate.Runtime
