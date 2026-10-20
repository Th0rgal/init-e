import InitECandidate.Runtime.PtSegAlGD
/-!
`process_transaction` spine drops 49-52: `al_keys = alloc(nkeys * 52 + 8)` (unchecked decoded count: only the
returned pointer `Ak ≥ Lo` is used) and the nested key-copy loops with the two `memcpy` calls at the cursor
`al_keys + k * 52` (20 address bytes, then 32 key bytes at `+ 20`). The cursor is fenced: the invariant
`Ak + 52 k ≤ DF + 8` holds at entry, each returning `memcpy` learns `dst + n ≤ DF + 8` (its last byte is in the
domain) before `k` advances, and with `DF + 8 ≤ 2^62` no destination wraps; every copy writes at or above `Lo`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A byte window starting at or above an 8-aligned `Lo` avoids every word below `Lo`. -/
theorem mwin_lo {Lo Dd x : BitVec 64} {N : Nat} (hLo8 : Lo.toNat % 8 = 0) (hLD : Lo.toNat ≤ Dd.toNat)
    (fit : Dd.toNat + N < 2 ^ 64) (hx : x.toNat < Lo.toNat) : ¬ MWin Dd N x := by
  rintro ⟨j,hj,e | e⟩
  · have : (Dd + BitVec.ofNat 64 j).toNat = Dd.toNat + j := by simp [BitVec.toNat_add]; omega
    rw [← e] at this; omega
  · have h1 := align_toNat (Dd + BitVec.ofNat 64 j)
    have : (Dd + BitVec.ofNat 64 j).toNat = Dd.toNat + j := by simp [BitVec.toNat_add]; omega
    rw [this,← e] at h1; omega

section mf
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}

/-- The actual `memcpy(dst, src, n)` at a fenced destination at or above `Lo`: on return `dst + n ≤ DF + 8`, the
globals are kept, and only `[dst, dst + n)` changes. -/
theorem memcpyF (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (Dd Nn : BitVec 64) (hDst : Lo.toNat ≤ Dd.toNat) (hDF8 : Dd.toNat ≤ DF + 8)
    (small : Nn.toNat + 32 < 2 ^ 64) (fit : Dd.toNat + Nn.toNat < 2 ^ 64) (M0 : Mem) (G0 : GA) :
    AQGD D B A w (fun _ => False)
      (fun L M G => (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧
        (∃ S : BitVec 64, L.lookup (ofString "src") = some (.val (.word S))) ∧
        L.lookup (ofString "n") = some (.val (.word Nn))) ∧ M = M0 ∧ G = G0)
      (fun _ _ _ => False)
      (fun _ M' G' => Dd.toNat + Nn.toNat ≤ DF + 8 ∧ G' = G0 ∧ ∀ x, ¬ MWin Dd Nn.toNat x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_memcpy) := by
  have h1 := aqgd_conseq (memcpy_win (Vn := fun _ => False) (A := A) (B := B) hF hDF Lo hLo8 hw Dd Nn hDst hDF8)
    (P' := fun L M G => (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧
        (∃ S : BitVec 64, L.lookup (ofString "src") = some (.val (.word S))) ∧
        L.lookup (ofString "n") = some (.val (.word Nn))) ∧ M = M0 ∧ G = G0)
    (fun _ _ _ h => ⟨h.1.1,h.1.2.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  have h2 : AQGD D B A w (fun _ => False)
      (fun L M G => (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧
        (∃ S : BitVec 64, L.lookup (ofString "src") = some (.val (.word S))) ∧
        L.lookup (ofString "n") = some (.val (.word Nn))) ∧ M = M0 ∧ G = G0)
      (fun _ _ _ => True) (fun _ M' G' => G' = G0 ∧ ∀ x, ¬ MWin Dd Nn.toNat x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_memcpy) :=
    aqgd_conseq (P := fun L M G => ∃ S : BitVec 64, (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧
        L.lookup (ofString "src") = some (.val (.word S)) ∧ L.lookup (ofString "n") = some (.val (.word Nn))) ∧
        M = M0 ∧ G = G0)
      (aqgd_exE (fun S => memcpy_wn Dd S Nn small (mwin_lo hLo8 hDst fit hw) M0 G0))
      (fun _ _ _ ⟨⟨hd,⟨S,hs⟩,hn⟩,hm⟩ => ⟨S,⟨hd,hs,hn⟩,hm⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  exact aqgd_conseq (aqgd_and h1 h2) (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ ⟨a,b⟩ => ⟨a,b⟩)

#print axioms memcpyF
end mf

section mc
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {Lo Nj : BitVec 64} {M0 : Mem}

/-- `memcpy(d, src, N)` at a fenced destination `dst L` at or above `Lo`, keeping `SI`; a return gives
`dst L + N ≤ DF + 8`. -/
theorem aqgd_call_memcpy_si {LP LQ : GA → Prop} (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (d src : ExpHOL 64) (Nn : BitVec 64) (hN : Nn.toNat < 2 ^ 32) (dst : GA → BitVec 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals →
      EV s d = some (.val (.word (dst s.locals))))
    (hsrc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, EV s src = some v → ∃ y : BitVec 64, v = .val (.word y))
    (hlo : ∀ L, LP L → Lo.toNat ≤ (dst L).toNat ∧ (dst L).toNat ≤ DF + 8)
    (hup : ∀ L, LP L → (dst L).toNat + Nn.toNat ≤ DF + 8 → LQ L) :
    AQGD D B A w (fun _ => False) (fun L M G => LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
      (fun L M G => LQ L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) RR
      (.call (some (none,none)) (ofString "memcpy") [d,src,.const Nn]) := by
  refine aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word (dst L0))) ∧
        (∃ S : BitVec 64, L.lookup (ofString "src") = some (.val (.word S))) ∧
        L.lookup (ofString "n") = some (.val (.word Nn))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (L0 : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (dst L0).toNat + Nn.toNat ≤ DF + 8 ∧ G' = G0' ∧ ∀ x, ¬ MWin (dst L0) Nn.toNat x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨lp,_⟩
    obtain ⟨lo,hi⟩ := hlo L0 lp
    exact aqgd_conseq (memcpyF hF hDF Lo hLo8 hw (dst L0) Nn lo hi (by omega) (by omega) M0' G0')
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs _ H hG ⟨lp,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,ev3,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    rw [hd s lp] at ev1
    simp only [Option.some.injEq] at ev1; subst ev1
    obtain ⟨y,rfl⟩ := hsrc s v2 ev2
    simp [EV,evalHOLExact] at ev3; subst ev3
    have e := callee_eq originalRuntimeCode_memcpy_lookup lookup
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),⟨y,by rw [e]; simp (config := {decide := true})⟩,
      by rw [e]; simp (config := {decide := true})⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,si⟩ ⟨hb,hG,fr⟩
    subst hG
    obtain ⟨lo,hi⟩ := hlo L lp
    exact ⟨hup L lp hb,si_mem si (fun x hx => fr x (mwin_lo hLo8 lo (by omega) hx))⟩

#print axioms aqgd_call_memcpy_si
end mc
end InitECandidate.Runtime
