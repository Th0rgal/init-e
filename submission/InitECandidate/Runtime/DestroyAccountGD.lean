import InitECandidate.Runtime.DestroyStorageGD
import InitECandidate.Runtime.StateCommitHeap
import InitECandidate.Runtime.OriginalDestroyStorageCode
/-!
Original `destroy_account(addr)` = `destroy_storage(addr); set_account(addr, 1)` in the fixed-domain triple over the
content-carrying registry `RegT`. `setAccountF_aqg`: `set_account` through `jset_aqg` with fixed layouts, keeping the
finer frame (below the entry heap, outside the journal and the account table's footprint); `tlay_eq`: a header in
memory determines the layout; `regT_of_reg`: a registry whose writes kept table `ko`'s header and arrays carries its
content again.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {w : BitVec 64} {SP0 P0 FM : BitVec 64} {G0 : GA}

set_option maxHeartbeats 4000000 in
/-- `set_account(addr, a)` on a registry with fixed layouts `l`: as `setAccount_aqg`, with the finer frame of
`jset_aqg` (memory below the entry heap kept outside the journal and the account table's canonical footprint). -/
theorem setAccountF_aqg (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (l : Fin n → TLay) (k : Fin n)
    (Ts : BitVec 64) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hck : c k = Ts + 16#64)
    (J C Nj H0 : BitVec 64) (pure : RegPure n c T Out H0 l) (M0 : Mem) (hm0 : RegMem n c T l M0)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) :
    AQG (JW SP0 P0 FM G0 J C) w (fun _ => True)
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ M = M0 ∧
        HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True)
      (fun _ M' G' => Nj.toNat < C.toNat ∧ G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧
        ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧
          ∀ x, x.toNat < H0.toNat → ¬ InJ J C x → ¬ (l k).canon (T k) H0 x → M' x = M0 x)
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
      G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧
      ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧
        ∀ x, x.toNat < H0.toNat → ¬ InJ J C x → ¬ (l k).canon (T k) H0 x → M' x = M0 x)
    (aqg_callSpec (Vn' := fun x => x ≠ ofString "old")
      (Pe := fun _ M0' G0' L M G => (∃ Kk V : BitVec 64, JL (T k) Kk V L) ∧ M = M0' ∧ G = G0')
      (RRe := fun _ M0' _ _ M' G' => Nj.toNat < C.toNat ∧
        G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧
        ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧
          ∀ x, x.toNat < H0.toNat → ¬ InJ J C x → ¬ (l k).canon (T k) H0 x → M' x = M0' x)
      _ _ _ _ _ originalRuntimeCode_journalSet_lookup (by simp) ?_ ?_
      (fun _ _ _ _ _ _ ⟨_,_,hM,_,_⟩ h => by subst hM; exact h))
    (aqg_return _ (fun _ _ _ _ _ h _ _ => h))
  · intro L0 M0' G0' ⟨_,_,hM,hH,hn⟩
    refine aqg_conseq (P := fun L M G => ∃ Kk, ∃ V, JL (T k) Kk V L ∧ RegMem n c T l M ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (aqg_ex (fun Kk => aqg_ex (fun V => jset_aqg n c T Out l k H0 pure Kk V J C Nj M0 hm0 p0 jfit hwJ hwP hOut jsep)))
      ?_ (fun _ _ _ _ => trivial) (fun v M' G' h => by rw [hM]; exact h)
    intro L M G ⟨⟨Kk,V,hj⟩,hM',hG⟩
    subst hG
    exact ⟨Kk,V,hj,by rw [hM',hM]; exact hm0,hM'.trans hM,hH,hn⟩
  · intro F s values callee rs aw G hG ⟨⟨A,hA⟩,⟨V,hV⟩,hM,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨eg,_⟩ := aw.1.2.2.2 (ofString "ts") (by decide)
    have hcell := (hm0 k).1
    rw [hck,← hM] at hcell
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

#print axioms setAccountF_aqg

/-- A table header in memory determines the layout (the bit count through `C = 2 ^ b`). -/
theorem tlay_eq {M : Mem} {T : BitVec 64} {l l' : TLay} (h : l.hdr M T) (h' : l'.hdr M T)
    (p : l.C.toNat = 2 ^ l.b) (p' : l'.C.toNat = 2 ^ l'.b) : l' = l := by
  obtain ⟨a0,a8,a16,a24,a32,a40,a48,a56,a64⟩ := h
  obtain ⟨b0,b8,b16,b24,b32,b40,b48,b56,b64⟩ := h'
  rw [a0] at b0; rw [a8] at b8; rw [a16] at b16; rw [a24] at b24; rw [a32] at b32; rw [a40] at b40
  rw [a48] at b48; rw [a56] at b56; rw [a64] at b64
  cases l; cases l'
  simp only [HolWordLab.word.injEq] at b0 b8 b16 b24 b32 b40 b48 b56 b64
  subst b0 b8 b16 b24 b32 b40 b48 b56 b64
  simp only at p p'
  rw [p] at p'
  have := Nat.pow_right_injective (le_refl 2) p'
  subst this
  rfl

variable {D : BitVec 64 → Prop} {B : Bool}

/-- A registry at `H'` whose writes kept table `ko`'s header and arrays carries `ko`'s content again. -/
theorem regT_of_reg {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H1 H' : BitVec 64} {M1 M' : Mem}
    {ko : Fin n} (l : Fin n → TLay) (pure : RegPure n c T Out H1 l) (tc : TCont D B M1 (T ko) (l ko))
    (ab : ∀ x, (l ko).arr x → x.toNat < H1.toNat) (reg : Reg n c T Out H' M') (hle : H1.toNat ≤ H'.toNat)
    (keepT : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
      M' x = M1 x) : RegT n c T Out H' M' D B ko := by
  obtain ⟨l',tA,sep,o⟩ := reg
  have tc' := tc.frame (pure.1 ko).1.cnt.le keepT
  have e : l' ko = l ko := tlay_eq (tcont_hdr tc') (tA ko).2.2.1 (pure.1 ko).1.pow (tA ko).2.1.pow
  refine ⟨l',⟨fun i => ⟨(tA i).2.1,(tA i).2.2.2⟩,sep,o⟩,fun i => ⟨(tA i).1,(tA i).2.2.1⟩,by rw [e]; exact tc',
    fun x hx => by rw [e] at hx; have := ab x hx; omega⟩

#print axioms tlay_eq
#print axioms regT_of_reg

/-- Exit of `destroy_account`. -/
def DAPost (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (J C SKB H0 : BitVec 64) (M0 : Mem) (M' : Mem) (G' : GA) : Prop :=
  ∃ H' : BitVec 64, HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ RegT n c T Out H' M' D B ko ∧
    (∃ Nj' : BitVec 64, G'.lookup (ofString "journal_n") = some (.val (.word Nj'))) ∧
    ∀ x, Out x → ¬ InJ J C x → ¬ SkWin SKB x → M' x = M0 x

section da
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA : Fin n}
  {Ts SKB J C Nj H0 : BitVec 64} {M0 : Mem}

set_option maxHeartbeats 16000000 in
/-- The original `destroy_account(addr)`: `destroy_storage(addr)` then `set_account(addr, 1)` (account table `kA`,
cell `ts + 16`), over the registry with the content of the outer storage table `ko`. -/
theorem destroyAccount_aqgd (ne : kd ≠ ko) (neA : kA ≠ ko) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64) (hcA : c kA = Ts + 16#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => True)
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => DAPost n c T Out ko D B J C SKB H0 M0 M' G')
      (sourceFunctionBody Guest.guestFn_destroy_account) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_destroy_account,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  -- destroy_storage(addr)
  refine aqgd_seq (Q := fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      DSPost n c T Out ko D B J C SKB H0 Nj M0 M G)
    (aqgd_callSpec (Vn' := fun x => x ≠ ofString "m" ∧ x ≠ ofString "s")
      (Pe := fun _ M0' _ L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0' ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (RRe := fun _ M0' _ _ M' G' => DSPost n c T Out ko D B J C SKB H0 Nj M0' M' G')
      _ _ _ _ _ originalRuntimeCode_destroyStorage_lookup (by simp)
      (fun _ M0' _ _ => destroyStorage_aqgd (M0 := M0') ne hTs hco hcd p0 jfit hwJ hwP hOut hwS hJO hSO jsep)
      ?_ ?_) ?_
  · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,reg,_,hH,hn⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,hA] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_destroyStorage_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,reg,rfl,hH,hn⟩
  · intro L M G v M' G' ⟨ha,_,hM,_,_⟩ post
    subst hM
    exact ⟨ha,post⟩
  -- set_account(addr, 1)
  refine aqgd_seq (Q := fun _ M' G' => DAPost n c T Out ko D B J C SKB H0 M0 M' G') ?_
    (aqgd_return _ (fun _ _ _ _ _ h _ _ => h))
  refine aqgd_conseq (P := fun L M G => ∃ q : (Fin n → TLay) × BitVec 64 × BitVec 64,
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ HeapIs G q.2.1 ∧
      H0.toNat ≤ q.2.1.toNat ∧ RegPure n c T Out q.2.1 q.1 ∧ RegMem n c T q.1 M ∧ TCont D B M (T ko) (q.1 ko) ∧
      (∀ x, (q.1 ko).arr x → x.toNat < q.2.1.toNat) ∧
      G.lookup (ofString "journal_n") = some (.val (.word q.2.2)) ∧
      ∀ x, Out x → ¬ InJ J C x → ¬ SkWin SKB x → M x = M0 x)
    (aqgd_ex (fun q => ?_)) (fun L M G ⟨ha,H,hH,hle,⟨l,pure,mem,tc,ab⟩,hn,fr⟩ => by
      rcases hn with hn | ⟨_,hn⟩
      · exact ⟨(l,H,Nj),ha,hH,hle,pure,mem,tc,ab,hn,fr⟩
      · exact ⟨(l,H,Nj + 1),ha,hH,hle,pure,mem,tc,ab,hn,fr⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  rcases q with ⟨l,H1,Nj'⟩
  dsimp only
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' _ L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      (∃ V : BitVec 64, L.lookup (ofString "a") = some (.val (.word V))) ∧ M = M0' ∧
      HeapIs G H1 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj')))
    (RRe := fun _ M0' _ _ M' G' => Nj'.toNat < C.toNat ∧
      G'.lookup (ofString "journal_n") = some (.val (.word (Nj' + 1))) ∧
      ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧
        ∀ x, x.toNat < H1.toNat → ¬ InJ J C x → ¬ (l kA).canon (T kA) H1 x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_setAccount_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,_,hle,pure,mem,_,_,_,_⟩
    exact aqgd_jws (aqgd_of_aqg (setAccountF_aqg n c T Out l kA Ts hTs hcA J C Nj' H1 pure M0' mem (by omega) jfit
      hwJ hwP hOut jsep)) (keepsSkBuf_of_installed originalRuntimeCode_setAccount_lookup (by decide))
  · intro F s values callee rs _ G hG ⟨⟨A,hA⟩,hH,_,_,_,_,_,hn,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_setAccount_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      ⟨1#64,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,hH,hn⟩
  · intro L M G v M' G' ⟨_,_,hle,pure,mem,tc,ab,_,frO⟩ ⟨_,hn',H',hH',hle',reg,fr⟩
    have lay := (pure.1 ko).1
    have ltH : ∀ x, Out x → x.toNat < H1.toNat := fun x ho => by
      by_contra h; exact pure.2.2 x ho ko (Or.inr (Or.inr (by omega)))
    have keepT : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
        M' x = M x := by
      intro x hx
      refine fr x ?_ (fun hj => pure.2.2 x (hJO x hj) ko (intabf_canon hx)) (pure.2.1 kA ko neA x ?_)
      · rcases hx with hh | ha
        · have := lay.hdrP; omega
        · exact ab x ha
      · rcases hx with hh | ha
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr ha)
    exact ⟨H',hH',le_trans hle hle',regT_of_reg l pure tc ab reg hle' keepT,⟨Nj' + 1,hn'⟩,
      fun x ho hj hsk => (fr x (ltH x ho) hj (pure.2.2 x ho kA)).trans (frO x ho hj hsk)⟩

#print axioms destroyAccount_aqgd
end da
end InitECandidate.Runtime
