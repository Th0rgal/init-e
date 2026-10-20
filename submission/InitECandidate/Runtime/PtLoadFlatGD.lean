import InitECandidate.Runtime.PtIdxAcctGD
/-!
Loaded values have as many words as their shape: a one-word load is one word, a four-word load four words
(for stores of loaded values with `aqgd_storeV`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem memLoad_one_flat {a : BitVec 64} {dom : BitVec 64 → Prop} {inst : DecidablePred dom}
    {mem : BitVec 64 → HolWordLab 64} {ctx : StructContextHOLM} {v : ValueHOL 64}
    (h : @memLoadHOLExact 64 _ .one a dom inst mem ctx = some v) :
    (flattenHOL v).length = 1 := by
  simp only [memLoadHOLExact] at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; simp [flattenHOL]
  · simp at h

theorem memLoads_ones_flat (k : Nat) {a : BitVec 64} {dom : BitVec 64 → Prop} {inst : DecidablePred dom}
    {mem : BitVec 64 → HolWordLab 64} {ctx : StructContextHOLM} {vs : List (ValueHOL 64)}
    (h : @memLoadsHOLExact 64 _ (List.replicate k .one) a dom inst mem ctx = some vs) :
    ((vs.map flattenHOL).flatten).length = k := by
  induction k generalizing a vs with
  | zero => simp [memLoadsHOLExact] at h; subst h; simp
  | succ k ih =>
    rw [List.replicate_succ] at h
    simp only [memLoadsHOLExact] at h
    split at h
    · rename_i v vs' h1 h2
      simp only [Option.some.injEq] at h; subst h
      simp only [List.map_cons,List.flatten_cons,List.length_append,memLoad_one_flat h1,ih h2]
      omega
    · simp at h

theorem ev_load_flat {F : Type} (s : PanSemStateFiniteExact 64 F) (k : Nat) (e : ExpHOL 64) (x : ValueHOL 64)
    (h : EV s (.load (.comb (List.replicate k .one)) e) = some x) : (flattenHOL x).length ≤ k := by
  unfold EV at h
  simp only [evalHOLExact] at h
  split at h
  · split at h
    · simp only [memLoadHOLExact] at h
      split at h
      · rename_i vs hv
        simp only [Option.some.injEq] at h; subst h
        simp only [flattenHOL]
        rw [memLoads_ones_flat k hv]
      · simp at h
    · simp at h
  · simp at h

theorem ev_load1_flat {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (x : ValueHOL 64)
    (h : EV s (.load .one e) = some x) : (flattenHOL x).length ≤ 1 := by
  unfold EV at h
  simp only [evalHOLExact] at h
  split at h
  · split at h
    · rw [memLoad_one_flat h]
    · simp at h
  · simp at h

#print axioms ev_load_flat
#print axioms ev_load1_flat
/-- A byte window inside `[D0, D0 + Z)` from an aligned base. -/
theorem mwin_in {D0 x : BitVec 64} {off nn Z : Nat} (hal : D0.toNat % 8 = 0) (fit : D0.toNat + Z < 2 ^ 64)
    (h : off + nn ≤ Z) (hx : MWin (D0 + BitVec.ofNat 64 off) nn x) : D0.toNat ≤ x.toNat ∧ x.toNat < D0.toNat + Z := by
  have e : (D0 + BitVec.ofNat 64 off).toNat = D0.toNat + off := by
    rw [BitVec.toNat_add]; simp; omega
  obtain ⟨j,hj,hx | hx⟩ := hx
  · have e2 : (D0 + BitVec.ofNat 64 off + BitVec.ofNat 64 j).toNat = D0.toNat + off + j := by
      rw [BitVec.toNat_add,e]; simp; omega
    subst hx; rw [e2]; omega
  · have e2 : (D0 + BitVec.ofNat 64 off + BitVec.ofNat 64 j).toNat = D0.toNat + off + j := by
      rw [BitVec.toNat_add,e]; simp; omega
    subst hx
    rw [panByteAlign_toNat64,e2]
    have := Nat.div_mul_le_self (D0.toNat + off + j) 8
    have h8 : D0.toNat ≤ (D0.toNat + off + j) / 8 * 8 := by
      have := Nat.le_div_iff_mul_le (show 0 < 8 by decide) |>.mpr (show D0.toNat / 8 * 8 ≤ D0.toNat + off + j by omega)
      omega
    omega

#print axioms mwin_in

section mc
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- `memcpy(ed, es, en)` with any source word. -/
theorem aqgd_call_memcpyWany {LP : GA → Prop} (ed es en : ExpHOL 64) (Dd N : BitVec 64) (M1 : Mem) (G1 : GA)
    (small : N.toNat + 32 < 2 ^ 64) (out : ¬ MWin Dd N.toNat w)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → ∀ vs, evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ed,es,en] =
        some vs → ∃ S : BitVec 64, vs = [.val (.word Dd),.val (.word S),.val (.word N)]) :
    AQGD D B A w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ G = G1 ∧ ∀ x, ¬ MWin Dd N.toNat x → M x = M1 x) RR
      (.call (some (none,none)) (ofString "memcpy") [ed,es,en]) := by
  refine aqgd_callSpecD (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧ (∃ S : BitVec 64,
        L.lookup (ofString "src") = some (.val (.word S))) ∧ L.lookup (ofString "n") = some (.val (.word N))) ∧
        M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      G' = G0' ∧ ∀ x, ¬ MWin Dd N.toNat x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' _
    exact aqgd_conseq (aqgd_of_window (Pe := fun L _ => L.lookup (ofString "dst") = some (.val (.word Dd)) ∧
        (∃ S : BitVec 64, L.lookup (ofString "src") = some (.val (.word S))) ∧
        L.lookup (ofString "n") = some (.val (.word N)))
      memcpy_body_globals_frame (by body_check Guest.guestFn_memcpy) (by body_check Guest.guestFn_memcpy)
      (MWin Dd N.toNat) (fun s _ ⟨hd,⟨S,hs⟩,hn⟩ x hx => memcpy_body_window s Dd S N x hd hs hn small hx) out M0' G0')
      (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)
  · intro F s values callee rs _ dom H hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨S,rfl⟩ := hargs s dom hM hG1 lp values args
    rw [pan_three_word_lookup _ _ (ofString "dst") (ofString "src") (ofString "n") _ _ _ _ (by decide) (by decide)
      (by decide) originalRuntimeCode_memcpy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      ⟨S,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨eG,fr⟩
    exact ⟨lp,by rw [eG,hG],fun x hx => by rw [fr x hx,hM]⟩

#print axioms aqgd_call_memcpyWany

/-- The actual `memzero(ed, en)` call statement: globals unchanged, memory outside the window unchanged. -/
theorem aqgd_call_memzeroW {LP : GA → Prop} (ed en : ExpHOL 64) (Dd N : BitVec 64) (M1 : Mem) (G1 : GA)
    (small : N.toNat + 32 < 2 ^ 64) (out : ¬ MWin Dd N.toNat w)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ed,en] =
        some [.val (.word Dd),.val (.word N)]) :
    AQGD D B A w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ G = G1 ∧ ∀ x, ¬ MWin Dd N.toNat x → M x = M1 x) RR
      (.call (some (none,none)) (ofString "memzero") [ed,en]) := by
  refine aqgd_callSpecD (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧ L.lookup (ofString "n") = some (.val (.word N))) ∧
        M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      G' = G0' ∧ ∀ x, ¬ MWin Dd N.toNat x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_memzero_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' _
    exact aqgd_conseq (memzero_wn Dd N small out M0' G0') (fun _ _ _ h => h) (fun _ _ _ _ => trivial)
      (fun _ _ _ h => h)
  · intro F s values callee rs _ dom H hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    have e := callee_eq originalRuntimeCode_memzero_lookup lookup
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨eG,fr⟩
    exact ⟨lp,by rw [eG,hG],fun x hx => by rw [fr x hx,hM]⟩

#print axioms aqgd_call_memzeroW
end mc
end InitECandidate.Runtime
