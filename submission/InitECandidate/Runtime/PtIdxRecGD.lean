import InitECandidate.Runtime.PtLoadFlatGD
/-!
The entry-initialisation block of `idx_start_account`: `rec = alloc(80)`, `memzero(rec, 80)`, the empty code hash
copied to `rec + 48`, and (for an existing pre-state account) the flag, nonce, balance and code hash copied in; all
writes are in fresh heap `[rec, rec + 80)`, so the block (with the tail) is a world step.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The fresh-block memory/globals state: heap above the 80 fresh bytes at `H3`, the journal counter and the
block-access-list globals kept, memory below `H3` as in `M3`. -/
def FBM (BA IA IS KB Ix H3 Nj : BitVec 64) (M3 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ H' : BitVec 64, HeapIs G H' ∧ H3.toNat + 80 ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G ∧
    ∀ x, x.toNat < H3.toNat → M x = M3 x

section fb
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop} {BA IA IS KB Ix H3 Nj : BitVec 64} {M3 : Mem}

/-- A statement writing only inside a window at or above `H3` (globals unchanged) keeps the fresh-block state. -/
theorem aqgd_fresh {LP : GA → Prop} {p : ProgHOL 64} (Win : BitVec 64 → Prop)
    (hWin : ∀ x, Win x → H3.toNat ≤ x.toNat)
    (h : ∀ M2 G2, FBM BA IA IS KB Ix H3 Nj M3 M2 G2 → AQGD D B A w Vn (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ G = G2 ∧ ∀ x, ¬ Win x → M x = M2 x) RR p) :
    AQGD D B A w Vn (fun L M G => LP L ∧ FBM BA IA IS KB Ix H3 Nj M3 M G)
      (fun L M G => LP L ∧ FBM BA IA IS KB Ix H3 Nj M3 M G) RR p :=
  aqgd_ghostR (fun M2 G2 fb => aqgd_conseq (h M2 G2 fb) (fun _ _ _ h => h)
    (fun L M G ⟨lp,hG,fr⟩ => by
      subst hG
      obtain ⟨H',hH,le,hE,hn,bg,fr0⟩ := fb
      exact ⟨lp,H',hH,le,hE,hn,bg,fun x hx => (fr x (fun hw => by have := hWin x hw; omega)).trans (fr0 x hx)⟩)
    (fun _ _ _ h => h))

#print axioms aqgd_fresh

/-- A store of at most `k` words at `a ≥ H3` keeps the fresh-block state. -/
theorem aqgd_freshStore {LP : GA → Prop} (d v : ExpHOL 64) (a : BitVec 64) (k : Nat)
    (hw : w.toNat < H3.toNat) (ha : H3.toNat ≤ a.toNat) (hak : a.toNat + 8 * k ≤ 33806089496)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → EV s d = some (.val (.word a)))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → ∀ x, EV s v = some x →
      (flattenHOL x).length ≤ k) :
    AQGD D B A w Vn (fun L M G => LP L ∧ FBM BA IA IS KB Ix H3 Nj M3 M G)
      (fun L M G => LP L ∧ FBM BA IA IS KB Ix H3 Nj M3 M G) RR (.store d v) := by
  have ej : ∀ j, j < k → (a + BitVec.ofNat 64 (8 * j)).toNat = a.toNat + 8 * j := fun j hj => by
    rw [BitVec.toNat_add]; simp; omega
  refine aqgd_fresh (fun x => ∃ j, j < k ∧ x = a + BitVec.ofNat 64 (8 * j)) (fun x ⟨j,hj,e⟩ => by
    subst e; rw [ej j hj]; omega) (fun M2 G2 _ => aqgd_storeV d v (fun s _ _ ⟨lp,hM,hG⟩ =>
      ⟨a,k,hd s lp,hv s lp,fun j hj e => by have := ej j hj; rw [← e] at this; omega,
        fun M' fr => ⟨lp,hG,fun x hx => by rw [← hM]; exact fr x (fun j hj e => hx ⟨j,hj,e⟩)⟩⟩))

#print axioms aqgd_freshStore
end fb
theorem ev_load1_word {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (x : ValueHOL 64)
    (h : EV s (.load .one e) = some x) : ∃ y : BitVec 64, x = .val (.word y) := by
  unfold EV at h
  simp only [evalHOLExact] at h
  split at h
  · split at h
    · simp only [memLoadHOLExact] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        rcases (s.memory _) with ⟨y⟩
        exact ⟨y,rfl⟩
      · simp at h
    · simp at h
  · simp at h

#print axioms ev_load1_word

/-- A memcpy argument list `[rec + 48, src, 32]` evaluates to three words when `src` evaluates to a word. -/
theorem mc48_args {F : Type} (s : PanSemStateFiniteExact 64 F) (es : ExpHOL 64) (R : BitVec 64)
    (hr : s.locals.lookup (ofString "rec") = some (.val (.word R)))
    (hs : ∀ x, EV s es = some x → ∃ y : BitVec 64, x = .val (.word y)) (vs : List (ValueHOL 64))
    (ev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "rec"),.const 48#64],es,.const 32#64] = some vs) :
    ∃ S : BitVec 64, vs = [.val (.word (R + 48#64)),.val (.word S),.val (.word 32#64)] := by
  obtain ⟨v1,vs1,rfl,e1,r1⟩ := evalList_cons' s _ _ _ ev
  obtain ⟨v2,vs2,rfl,e2,r2⟩ := evalList_cons' s _ _ _ r1
  obtain ⟨v3,vs3,rfl,e3,r3⟩ := evalList_cons' s _ _ _ r2
  have := evalList_nil' s _ r3; subst this
  simp [EV,evalHOLExact,evalListHOLExact,hr,wordOpHOL,wordOp,valueIsWord,valueWord] at e1
  simp [EV,evalHOLExact] at e3
  obtain ⟨S,rfl⟩ := hs v2 e2
  subst e1 e3
  exact ⟨S,rfl⟩

#print axioms mc48_args

section rb
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop} {Nj : BitVec 64}

/-- The `idx_start_account` tail program. -/
def idxAcctTailP : ProgHOL 64 :=
  (ProgHOL.call (some (none,none)) (ofString "st_le64") [.var .local (ofString "kb"),
      .var .global (ofString "bal_index")]).seq
    ((ProgHOL.call (some (none,none)) (ofString "memcpy") [.op .add [.var .local (ofString "kb"),.const 8#64],
        .var .local (ofString "addr"),.const 20#64]).seq
      ((ProgHOL.call (some (none,none)) (ofString "htab_set") [.var .global (ofString "bal_idx_accts"),
          .var .local (ofString "kb"),.var .local (ofString "rec")]).seq
        (.return (.var .local (ofString "rec")))))

/-- The entry block from `rec = alloc(80)` to the end of `idx_start_account`. -/
def idxAcctRecP : ProgHOL 64 :=
  .decCall (ofString "rec") .one (ofString "alloc") [.const 80#64]
    ((ProgHOL.call (some (none,none)) (ofString "memzero") [.var .local (ofString "rec"),.const 80#64]).seq
      ((ProgHOL.call (some (none,none)) (ofString "memcpy") [.op .add [.var .local (ofString "rec"),.const 48#64],
          .var .global (ofString "empty_code_hash"),.const 32#64]).seq
        ((ProgHOL.ite (.cmp .notEqual (.var .local (ofString "pre")) (.const 1#64))
            ((ProgHOL.store (.var .local (ofString "rec")) (.const 1#64)).seq
              ((ProgHOL.store (.op .add [.var .local (ofString "rec"),.const 8#64])
                  (.load .one (.op .add [.var .local (ofString "pre"),.const 0#64]))).seq
                ((ProgHOL.store (.op .add [.var .local (ofString "rec"),.const 16#64])
                    (.load (.comb [.one,.one,.one,.one]) (.op .add [.var .local (ofString "pre"),.const 8#64]))).seq
                  (ProgHOL.call (some (none,none)) (ofString "memcpy") [.op .add [.var .local (ofString "rec"),
                    .const 48#64],.load .one (.op .add [.var .local (ofString "pre"),.const 48#64]),.const 32#64]))))
            .skip).seq idxAcctTailP)))

theorem idxAcctRec_aqgd (bk : BalKeep) (wsf : WsIFrame WsI) (A Y : BitVec 64) {ADs : Set (BitVec 64)}
    {Rg : BalK → BitVec 64 → Prop} {H3 : BitVec 64} {Rr Ow : BitVec 64 → Prop} {M3 : Mem} {G3 : GA}
    (u3 : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H3 Rr Ow M3 G3)
    (hwP : w.toNat < P0.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w) (hwR : ¬ Rr w) (hwO : ¬ Ow w) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (L.lookup (ofString "kb") = some (.val (.word KB)) ∧
        L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "pre") = some (.val (.word Y))) ∧
        M = M3 ∧ G = G3) (fun _ _ _ => False)
      (fun v M G => (∃ y : BitVec 64, v = .val (.word y)) ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H3 Rr Ow M3 M G) idxAcctRecP := by
  refine uw_heapFact u3 (fun ⟨p0,hHE,hal⟩ => ?_)
  have hw3 : w.toNat < H3.toNat := by omega
  have u3' := u3
  obtain ⟨hH3,hn3,hB3,_⟩ := u3'
  let LPf : GA → Prop := fun L => ITL KB A H3 L ∧ L.lookup (ofString "pre") = some (.val (.word Y))
  unfold idxAcctRecP
  refine aqgd_decCall_alloc_b bk BA IA IS KB Ix
    (Pc := fun L M G => (LPf L ∧ FBM BA IA IS KB Ix H3 Nj M3 M G) ∧ H3.toNat + 80 ≤ 33806089496)
    (Qc := fun _ _ _ => False) (ofString "rec") 80#64 H3 Nj M3 G3 hH3 hn3 hB3 ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro L H' G' ⟨lk,la,lp⟩ hH' le hE _ hn' bg'
    have e80 : (80#64 : BitVec 64).toNat = 80 := by decide
    rw [e80] at le
    exact ⟨⟨⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact lk,by rw [lookup_update_ne' _ _ (by decide)]; exact la,
      lookup_update_eq' _ _ _⟩,by rw [lookup_update_ne' _ _ (by decide)]; exact lp⟩,
      H',hH',le,hE,hn',bg',fun _ _ => rfl⟩,by omega⟩
  refine aqgd_pureE (fun hfit => ?_)
  have lbW : ∀ (off nn : Nat), off + nn ≤ 80 → ∀ x, MWin (H3 + BitVec.ofNat 64 off) nn x → H3.toNat ≤ x.toNat :=
    fun off nn h x hx => (mwin_in (Z := 80) hal (by omega) h hx).1
  have outW : ∀ (off nn : Nat), off + nn ≤ 80 → ¬ MWin (H3 + BitVec.ofNat 64 off) nn w := fun off nn h hx => by
    have := lbW off nn h w hx; omega
  have lr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LPf s.locals →
      s.locals.lookup (ofString "rec") = some (.val (.word H3)) := fun s h => h.1.2.2
  -- memzero(rec, 80)
  refine aqgd_seq (aqgd_fresh (MWin H3 80) (fun x hx => lbW 0 80 (by decide) x (by simpa using hx))
    (fun M2 G2 _ => aqgd_call_memzeroW (LP := LPf) _ _ H3 80#64 M2 G2 (by decide)
      (fun hx => outW 0 80 (by decide) (by simpa using hx)) (fun s _ _ _ h => by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,lr s h]))) ?_
  -- memcpy(rec + 48, src, 32) for a word-valued source
  have mc48 : ∀ {RR' : ValueHOL 64 → Mem → GA → Prop} (es : ExpHOL 64), (∀ {F : Type}
      (s : PanSemStateFiniteExact 64 F), JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc s.globals → ∀ x, EV s es = some x →
        ∃ y : BitVec 64, x = .val (.word y)) →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPf L ∧ FBM BA IA IS KB Ix H3 Nj M3 M G) (fun L M G => LPf L ∧ FBM BA IA IS KB Ix H3 Nj M3 M G) RR'
      (.call (some (none,none)) (ofString "memcpy") [.op .add [.var .local (ofString "rec"),.const 48#64],es,
        .const 32#64]) := fun es hes =>
    aqgd_fresh (MWin (H3 + 48#64) 32) (fun x hx => lbW 48 32 (by decide) x hx)
      (fun M2 G2 _ => by
        refine aqgd_of_arenaFact (Φ := JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc G2)
          (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact aw) (fun aw2 => ?_)
        exact aqgd_call_memcpyWany (LP := LPf) _ _ _ (H3 + 48#64) 32#64 M2 G2 (by decide)
          (outW 48 32 (by decide)) (fun s _ _ hg h vs ev => mc48_args s es H3 (lr s h)
            (fun x hx => hes s (by rw [hg]; exact aw2) x hx) vs ev))
  -- memcpy(rec + 48, empty_code_hash, 32): a static global word
  refine aqgd_seq (mc48 _ (fun s aw x hx => by
    obtain ⟨eg,y,hy⟩ := aw.1.1.1.1.1.2.2.2 (ofString "empty_code_hash") (by decide)
    simp [EV,evalHOLExact,eg,hy] at hx
    exact ⟨y,hx.symm⟩)) ?_
  have eo : ∀ o : Nat, o < 80 → (H3 + BitVec.ofNat 64 o).toNat = H3.toNat + o := fun o ho => by
    rw [BitVec.toNat_add]; simp; omega
  refine aqgd_seq (Q := fun L M G => LPf L ∧ FBM BA IA IS KB Ix H3 Nj M3 M G)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  · refine aqgd_conseq (P := fun L M G => LPf L ∧ FBM BA IA IS KB Ix H3 Nj M3 M G) ?_ (fun _ _ _ h => h.1)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_seq (aqgd_freshStore _ _ H3 1 hw3 (le_refl _) (by omega)
      (fun s h => by simp [EV,evalHOLExact,lr s h])
      (fun s _ x hx => by simp [EV,evalHOLExact] at hx; subst hx; simp [flattenHOL])) ?_
    refine aqgd_seq (aqgd_freshStore _ _ (H3 + 8#64) 1 hw3 (by rw [eo 8 (by decide)]; omega)
      (by rw [eo 8 (by decide)]; omega)
      (fun s h => by simp [EV,evalHOLExact,evalListHOLExact,lr s h,wordOpHOL,wordOp,valueIsWord,valueWord])
      (fun s _ x hx => ev_load1_flat s _ x hx)) ?_
    refine aqgd_seq (aqgd_freshStore _ _ (H3 + 16#64) 4 hw3 (by rw [eo 16 (by decide)]; omega)
      (by rw [eo 16 (by decide)]; omega)
      (fun s h => by simp [EV,evalHOLExact,evalListHOLExact,lr s h,wordOpHOL,wordOp,valueIsWord,valueWord])
      (fun s _ x hx => ev_load_flat s 4 _ x hx)) ?_
    exact mc48 _ (fun s _ x hx => ev_load1_word s _ x hx)
  refine aqgd_ghostR (fun M4 G4 fb => ?_)
  obtain ⟨H4,hH4,le4,_,hn4,bg4,fr4⟩ := fb
  obtain ⟨A4,R4,H4',Rr4,Ow4,u4,le',sub',gr',grR',grO',fr'⟩ :=
    ust_of_fresh (M := M4) (G := G4) wsf u3 (by omega : H3.toNat ≤ H4.toNat) hH4 hn4 bg4 fr4
  refine aqgd_conseq (idxAcctTail_aqgd bk wsf A H3 u4 hwP (fun k hk h => ?_) (fun h => ?_) (fun h => ?_))
    (fun L M G ⟨⟨itl,_⟩,hM,hG⟩ => ⟨itl,hM,hG⟩) (fun _ _ _ h => h)
    (fun v M G ⟨hv,s2⟩ => ⟨⟨H3,hv⟩,ust_trans le' sub' gr' grR' grO' fr' s2⟩)
  · rcases gr' k hk w h with ⟨l1,h1⟩ | ⟨a1,_⟩
    · exact hwk k l1 h1
    · omega
  · rcases grR' w h with h | ⟨a1,_⟩
    · exact hwR h
    · omega
  · rcases grO' w h with h | ⟨a1,_⟩
    · exact hwO h
    · omega

#print axioms idxAcctRec_aqgd

end rb
end InitECandidate.Runtime
