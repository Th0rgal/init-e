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

/-- Key-copy cursor invariant with slack `b`: `al_keys = Ak ≥ Lo`, `k = K`, `Ak + 52 K + b ≤ DF + 8`. -/
def LKI (Ix S Lo : BitVec 64) (DF b : Nat) (L : GA) : Prop :=
  LTe Ix S Lo L ∧ ∃ Ak K : BitVec 64, L.lookup (ofString "al_keys") = some (.val (.word Ak)) ∧
    L.lookup (ofString "k") = some (.val (.word K)) ∧ Lo.toNat ≤ Ak.toNat ∧ Ak.toNat + 52 * K.toNat + b ≤ DF + 8

theorem lki_upd {Ix S Lo : BitVec 64} {DF b : Nat} {L : GA} (h : LKI Ix S Lo DF b L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "index" ≠ x) (h2 : ofString "sender" ≠ x) (h3 : ofString "te" ≠ x) (h4 : ofString "al_keys" ≠ x)
    (h5 : ofString "k" ≠ x) : LKI Ix S Lo DF b (L.update (x,v)) :=
  let ⟨lt,Ak,K,hA,hK,a,c⟩ := h
  ⟨lte_upd lt x v h1 h2 h3,Ak,K,by rw [lookup_update_ne' _ _ h4]; exact hA,by rw [lookup_update_ne' _ _ h5]; exact hK,a,c⟩

theorem lki_res {Ix S Lo : BitVec 64} {DF b : Nat} {L : GA} (h : LKI Ix S Lo DF b L) (x : MlS)
    (o : Option (ValueHOL 64)) (h1 : ofString "index" ≠ x) (h2 : ofString "sender" ≠ x) (h3 : ofString "te" ≠ x)
    (h4 : ofString "al_keys" ≠ x) (h5 : ofString "k" ≠ x) : LKI Ix S Lo DF b (L.resVarEq (x,o)) :=
  let ⟨lt,Ak,K,hA,hK,a,c⟩ := h
  ⟨lte_res lt x o h1 h2 h3,Ak,K,by rw [resVarEq_lookup_ne' _ _ _ _ h4]; exact hA,
    by rw [resVarEq_lookup_ne' _ _ _ _ h5]; exact hK,a,c⟩

/-- The two copy destinations as functions of the locals. -/
def kDst1 (L : GA) : BitVec 64 := wordOf L (ofString "al_keys") + wordOf L (ofString "k") * 52#64
def kDst2 (L : GA) : BitVec 64 := wordOf L (ofString "al_keys") + wordOf L (ofString "k") * 52#64 + 20#64

theorem kdst_nat {Ix S Lo : BitVec 64} {DF b : Nat} {L : GA} (hDF : DF + 8 ≤ 2 ^ 62) (h : LKI Ix S Lo DF b L) :
    (kDst1 L).toNat = (wordOf L (ofString "al_keys")).toNat + 52 * (wordOf L (ofString "k")).toNat ∧
    (kDst2 L).toNat = (wordOf L (ofString "al_keys")).toNat + 52 * (wordOf L (ofString "k")).toNat + 20 ∧
    Lo.toNat ≤ (wordOf L (ofString "al_keys")).toNat ∧
    (wordOf L (ofString "al_keys")).toNat + 52 * (wordOf L (ofString "k")).toNat + b ≤ DF + 8 := by
  obtain ⟨_,Ak,K,hA,hK,lo,hb⟩ := h
  unfold kDst1 kDst2
  rw [wordOf_eq hA,wordOf_eq hK]
  have e1 : (Ak + K * 52#64).toNat = Ak.toNat + 52 * K.toNat := by simp [BitVec.toNat_add,BitVec.toNat_mul]; omega
  refine ⟨e1,?_,lo,hb⟩
  have : (Ak + K * 52#64 + 20#64).toNat = (Ak + K * 52#64).toNat + 20 := by simp [BitVec.toNat_add]; omega
  rw [this,e1]

section kl
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Nj : BitVec 64} {M0 : Mem}

/-- The inner key-copy body: the two fenced copies, `k = k + 1`, `j = j + 1`. -/
theorem keyInnerBody (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Ix S : BitVec 64) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LKI Ix S Lo DF 0 L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ True)
      (fun L M G => LKI Ix S Lo DF 0 L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) RR
      (.seq (.call (some (none,none)) (ofString "memcpy") [(.op .add [(.var .local (ofString "al_keys")),(.panop .mul [(.var .local (ofString "k")),(.const 52)])]),(.load .one (.op .add [(.var .local (ofString "acc2")),(.const 0)])),(.const 20)])
      (.seq (.call (some (none,none)) (ofString "memcpy") [(.op .add [(.var .local (ofString "al_keys")),(.panop .mul [(.var .local (ofString "k")),(.const 52)]),(.const 20)]),(.op .add [(.load .one (.op .add [(.var .local (ofString "acc2")),(.const 8)])),(.panop .mul [(.var .local (ofString "j")),(.const 32)])]),(.const 32)])
      (.seq (.assign .local (ofString "k") (.op .add [(.var .local (ofString "k")),(.const 1)]))
        (.assign .local (ofString "j") (.op .add [(.var .local (ofString "j")),(.const 1)]))))) := by
  have hDF' : DF ≤ 2 ^ 62 := by omega
  refine aqgd_conseq (P := fun L M G => LKI Ix S Lo DF 0 L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ?_
    (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_seq (aqgd_call_memcpy_si (LP := LKI Ix S Lo DF 0) (LQ := LKI Ix S Lo DF 20) hF hDF' hLo8 hw _ _ 20#64
    (by decide) kDst1 ?_ (fun s v ev => ev_load_one_word s _ v ev) ?_ ?_) ?_
  · intro F s ⟨_,Ak,K,hA,hK,_,_⟩
    unfold kDst1; rw [wordOf_eq hA,wordOf_eq hK]
    simp [EV,evalHOLExact,evalListHOLExact,hA,hK,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  · intro L h
    obtain ⟨e1,_,lo,hb⟩ := kdst_nat hDF h
    exact ⟨by omega,by omega⟩
  · intro L h hb
    obtain ⟨lt,Ak,K,hA,hK,lo,hb0⟩ := h
    unfold kDst1 at hb; rw [wordOf_eq hA,wordOf_eq hK] at hb
    have e : (Ak + K * 52#64).toNat = Ak.toNat + 52 * K.toNat := by
      simp [BitVec.toNat_add,BitVec.toNat_mul]; omega
    have : (20#64).toNat = 20 := rfl
    exact ⟨lt,Ak,K,hA,hK,lo,by omega⟩
  refine aqgd_seq (aqgd_call_memcpy_si (LP := LKI Ix S Lo DF 20) (LQ := LKI Ix S Lo DF 52) hF hDF' hLo8 hw _ _ 32#64
    (by decide) kDst2 ?_ (fun s v ev => ev_op_word s _ _ v ev) ?_ ?_) ?_
  · intro F s ⟨_,Ak,K,hA,hK,_,_⟩
    unfold kDst2; rw [wordOf_eq hA,wordOf_eq hK]
    simp [EV,evalHOLExact,evalListHOLExact,hA,hK,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,BitVec.add_assoc]
  · intro L h
    obtain ⟨_,e2,lo,hb⟩ := kdst_nat hDF h
    exact ⟨by omega,by omega⟩
  · intro L h hb
    obtain ⟨lt,Ak,K,hA,hK,lo,hb0⟩ := h
    unfold kDst2 at hb; rw [wordOf_eq hA,wordOf_eq hK] at hb
    have e : (Ak + K * 52#64 + 20#64).toNat = Ak.toNat + 52 * K.toNat + 20 := by
      simp [BitVec.toNat_add,BitVec.toNat_mul]; omega
    have : (32#64).toNat = 32 := rfl
    exact ⟨lt,Ak,K,hA,hK,lo,by omega⟩
  refine aqgd_seq (aqgd_assignLocal (Q := fun L M G => LKI Ix S Lo DF 0 L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
    _ _ (fun s v _ _ ⟨⟨lt,Ak,K,hA,hK,lo,hb⟩,si⟩ _ ev => ?_)) ?_
  · simp [EV,evalHOLExact,evalListHOLExact,hK,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have e : (K + 1#64).toNat = K.toNat + 1 := by simp [BitVec.toNat_add]; omega
    exact ⟨⟨lte_upd lt _ _ (by decide) (by decide) (by decide),Ak,K + 1#64,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hA,lookup_update_eq' _ _ _,lo,by rw [e]; omega⟩,si⟩
  exact aqgd_assignLocal _ _ (fun s v _ _ pre _ _ =>
    ⟨lki_upd pre.1 _ v (by decide) (by decide) (by decide) (by decide) (by decide),pre.2⟩)

#print axioms keyInnerBody

/-- The outer key-copy body: `acc2`, `ns`, `j`, the inner loop, `i = i + 1`. -/
theorem keyOuterBody (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Ix S : BitVec 64) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LKI Ix S Lo DF 0 L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ True)
      (fun L M G => LKI Ix S Lo DF 0 L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) RR
      (.dec (ofString "acc2") .one (.op .add [(.load .one (.op .add [(.var .local (ofString "tx")),(.const 208)])),(.panop .mul [(.var .local (ofString "i")),(.const 24)])]) (.dec (ofString "ns") .one (.load .one (.op .add [(.var .local (ofString "acc2")),(.const 16)])) (.dec (ofString "j") .one (.const 0) (.seq (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))) (.seq (.call (some (none,none)) (ofString "memcpy") [(.op .add [(.var .local (ofString "al_keys")),(.panop .mul [(.var .local (ofString "k")),(.const 52)])]),(.load .one (.op .add [(.var .local (ofString "acc2")),(.const 0)])),(.const 20)]) (.seq (.call (some (none,none)) (ofString "memcpy") [(.op .add [(.var .local (ofString "al_keys")),(.panop .mul [(.var .local (ofString "k")),(.const 52)]),(.const 20)]),(.op .add [(.load .one (.op .add [(.var .local (ofString "acc2")),(.const 8)])),(.panop .mul [(.var .local (ofString "j")),(.const 32)])]),(.const 32)]) (.seq (.assign .local (ofString "k") (.op .add [(.var .local (ofString "k")),(.const 1)])) (.assign .local (ofString "j") (.op .add [(.var .local (ofString "j")),(.const 1)])))))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)])))))) := by
  let I := fun L M G => LKI Ix S Lo DF 0 L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G
  have dk : ∀ (x : MlS), ofString "index" ≠ x → ofString "sender" ≠ x → ofString "te" ≠ x →
      ofString "al_keys" ≠ x → ofString "k" ≠ x → ∀ {body : ProgHOL 64} (sh : ShapeHOL) (init : ExpHOL 64)
      {P : GA → Mem → GA → Prop}, (∀ L M G, P L M G → I L M G) →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) I I RR body →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) P I RR (.dec x sh init body) :=
    fun x h1 h2 h3 h4 h5 _ sh init _ hP hb => aqgd_dec (Pb := I) (Qb := I) _ _ _ (fun h => h.elim)
      (fun s v _ _ _ pre _ _ _ => ⟨lki_upd (hP _ _ _ pre).1 _ v h1 h2 h3 h4 h5,(hP _ _ _ pre).2⟩) hb
      (fun _ _ _ _ _ _ _ q => ⟨lki_res q.1 _ _ h1 h2 h3 h4 h5,q.2⟩)
  refine dk _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ (fun _ _ _ h => h.1) ?_
  refine dk _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ (fun _ _ _ h => h) ?_
  refine dk _ (by decide) (by decide) (by decide) (by decide) (by decide) _ _ (fun _ _ _ h => h) ?_
  refine aqgd_seq (aqgd_whileI _ (keyInnerBody hF hDF hLo8 hw Ix S)) ?_
  exact aqgd_assignLocal _ _ (fun s v _ _ pre _ _ =>
    ⟨lki_upd pre.1 _ v (by decide) (by decide) (by decide) (by decide) (by decide),pre.2⟩)

#print axioms keyOuterBody

/-- Spine drops 49-52 of the actual `process_transaction`. -/
theorem ptSegKeys {QM : Mem → GA → Prop} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat) (Ix S : BitVec 64) {cont : ProgHOL 64}
    (hcont : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LTe Ix S Lo L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) (fun _ M G => QM M G) RR
      (.decCall (ofString "al_keys") .one (ofString "alloc") [(.op .add [(.panop .mul [(.var .local (ofString "nkeys")),(.const 52)]),(.const 8)])]
      (.dec (ofString "k") .one (.const 0)
      (.seq (.assign .local (ofString "i") (.const 0))
      (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) (.dec (ofString "acc2") .one (.op .add [(.load .one (.op .add [(.var .local (ofString "tx")),(.const 208)])),(.panop .mul [(.var .local (ofString "i")),(.const 24)])]) (.dec (ofString "ns") .one (.load .one (.op .add [(.var .local (ofString "acc2")),(.const 16)])) (.dec (ofString "j") .one (.const 0) (.seq (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))) (.seq (.call (some (none,none)) (ofString "memcpy") [(.op .add [(.var .local (ofString "al_keys")),(.panop .mul [(.var .local (ofString "k")),(.const 52)])]),(.load .one (.op .add [(.var .local (ofString "acc2")),(.const 0)])),(.const 20)]) (.seq (.call (some (none,none)) (ofString "memcpy") [(.op .add [(.var .local (ofString "al_keys")),(.panop .mul [(.var .local (ofString "k")),(.const 52)]),(.const 20)]),(.op .add [(.load .one (.op .add [(.var .local (ofString "acc2")),(.const 8)])),(.panop .mul [(.var .local (ofString "j")),(.const 32)])]),(.const 32)]) (.seq (.assign .local (ofString "k") (.op .add [(.var .local (ofString "k")),(.const 1)])) (.assign .local (ofString "j") (.op .add [(.var .local (ofString "j")),(.const 1)])))))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)])))))))
        cont)))) := by
  refine aqgd_decCall_allocE_si (LP' := fun L => LTe Ix S Lo L ∧ ∃ Ak : BitVec 64,
      L.lookup (ofString "al_keys") = some (.val (.word Ak)) ∧ Lo.toNat ≤ Ak.toNat ∧ Ak.toNat ≤ 33806089496)
    _ _ (fun s x ev => ev_op_word s _ _ x ev)
    (fun L Hb lp le hi _ => ⟨lte_upd lp _ _ (by decide) (by decide) (by decide),Hb,lookup_update_eq' _ _ _,le,hi⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_dec (Pb := fun L M G => LKI Ix S Lo DF 0 L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
    (Qb := fun _ M G => QM M G) _ _ _ (fun h => h.elim) (fun s v _ _ _ pre _ ev _ => ?_) ?_
    (fun _ _ _ _ _ _ _ h => h)
  · simp [EV,evalHOLExact] at ev
    subst ev
    obtain ⟨⟨lt,Ak,hA,lo,hi⟩,si⟩ := pre
    exact ⟨⟨lte_upd lt _ _ (by decide) (by decide) (by decide),Ak,0#64,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hA,lookup_update_eq' _ _ _,lo,by simp; omega⟩,si⟩
  refine aqgd_seq (aqgd_assignLocal (Q := fun L M G => LKI Ix S Lo DF 0 L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
    _ _ (fun s v _ _ pre _ _ =>
      ⟨lki_upd pre.1 _ v (by decide) (by decide) (by decide) (by decide) (by decide),pre.2⟩)) ?_
  refine aqgd_seq (aqgd_whileI _ (keyOuterBody hF hDF hLo8 hw Ix S)) ?_
  exact aqgd_conseq hcont (fun _ _ _ h => ⟨h.1.1,h.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms ptSegKeys
end kl
end InitECandidate.Runtime
