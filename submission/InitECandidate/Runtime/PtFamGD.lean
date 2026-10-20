import InitECandidate.Runtime.PtUnionOGD
import InitECandidate.Runtime.HtabUnionSites
import InitECandidate.Runtime.PtSufEGD
/-!
Families of block tables indexed by their addresses: `BTF R Os H M` says every table `t ∈ R` is a `TabO (Os t)` table
(canonical footprint at the heap pointer `H`), owned regions lie below `H` and are pairwise disjoint. A union into one
member grows its owned region by fresh heap and keeps every other member (frame). `MHS` is the state of a sequence of
such unions from the entry family `Os0` at heap `H0`: words outside every entry region below `H0` are kept.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A family of owned-region tables. -/
def BTF (R : Set (BitVec 64)) (Os : BitVec 64 → BitVec 64 → Prop) (H : BitVec 64) (M : Mem) : Prop :=
  (∀ t ∈ R, TabO (Os t) t H M) ∧ (∀ t ∈ R, ∀ x, Os t x → x.toNat < H.toNat) ∧
  (∀ t ∈ R, ∀ t' ∈ R, t ≠ t' → ∀ x, Os t x → ¬ Os t' x)

/-- A union into the member `j`: the family at the exit heap pointer with `j`'s region grown by `[H, H')`. -/
theorem btf_union {R : Set (BitVec 64)} {Os : BitVec 64 → BitVec 64 → Prop} {H Nj : BitVec 64} {M M' : Mem} {G' : GA}
    {j : BitVec 64} (hj : j ∈ R) (f : BTF R Os H M) (u : UOS (Os j) j H Nj M M' G') :
    ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat ≤ H'.toNat ∧
      BTF R (fun t x => Os t x ∨ (t = j ∧ H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) H' M' ∧
      G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∀ x, ¬ Os j x → x.toNat < H.toNat → M' x = M x := by
  obtain ⟨H',hH',le,tj,hn,fr⟩ := u
  obtain ⟨ft,fb,fd⟩ := f
  refine ⟨H',hH',le,⟨fun t ht => ?_,fun t ht x hx => ?_,fun t ht t' ht' ne x hx hx' => ?_⟩,hn,fr⟩
  · by_cases e : t = j
    · subst e
      exact tabO_sub tj (fun x h => by
        rcases h with h | ⟨h1,h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨rfl,h1,h2⟩)
    · exact tabO_sub (tabO_mono (tabO_frame (ft t ht) (fun x hx => fr x (fun h => fd t ht j hj e x hx h)
        (fb t ht x hx))) le) (fun x h => Or.inl h)
  · rcases hx with h | ⟨_,_,h2⟩
    · have := fb t ht x h; omega
    · exact h2
  · rcases hx with h | ⟨e,h1,_⟩ <;> rcases hx' with h' | ⟨e',h1',_⟩
    · exact fd t ht t' ht' ne x h h'
    · have := fb t ht x h; omega
    · have := fb t' ht' x h'; omega
    · exact ne (e.trans e'.symm)

#print axioms btf_union

/-- State of a sequence of unions into members of a family entered as `Os0` at heap `H0` with memory `M1`. -/
def MHS (R : Set (BitVec 64)) (Os0 : BitVec 64 → BitVec 64 → Prop) (H0 Nj : BitVec 64) (M1 M : Mem) (G : GA) :
    Prop :=
  ∃ (H : BitVec 64) (Os : BitVec 64 → BitVec 64 → Prop), HeapIs G H ∧ H0.toNat ≤ H.toNat ∧ BTF R Os H M ∧
    (∀ t x, Os t x → Os0 t x ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < H.toNat)) ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
    ∀ x, (∀ t ∈ R, ¬ Os0 t x) → x.toNat < H0.toNat → M x = M1 x

theorem mhs_init {R : Set (BitVec 64)} {Os0 : BitVec 64 → BitVec 64 → Prop} {H0 Nj : BitVec 64} {M1 : Mem} {G : GA}
    (f : BTF R Os0 H0 M1) (hH : HeapIs G H0) (hn : G.lookup (ofString "journal_n") = some (.val (.word Nj))) :
    MHS R Os0 H0 Nj M1 M1 G :=
  ⟨H0,Os0,hH,le_refl _,f,fun _ _ h => Or.inl h,hn,fun _ _ _ => rfl⟩

section mh
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A pure conjunct of the precondition may be assumed. -/
theorem aqgd_preP {φ : Prop} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64} (h : φ → AQGD D B A w Vn P Q RR p) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ φ) Q RR p :=
  fun F s code dom aw sl G hG ⟨pre,f⟩ => h f F s code dom aw sl G hG pre
end mh

section mu
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `htab_union_into(lds(bs + kb), lds(ts + ks))` into the family member `j` stored at `bs + kb`; both
cells lie outside every entry region below `H0`. -/
theorem aqgd_call_unionMH {LP : GA → Prop} (R : Set (BitVec 64)) (Os0 : BitVec 64 → BitVec 64 → Prop)
    (j kb ks Bs Ts H0 Nj y : BitVec 64) (M1 : Mem) (hj : j ∈ R)
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (db : D (Bs + kb)) (cb : M1 (Bs + kb) = .word j) (ob : ∀ t ∈ R, ¬ Os0 t (Bs + kb))
    (lb : (Bs + kb).toNat < H0.toNat)
    (dt : D (Ts + ks)) (ct : M1 (Ts + ks) = .word y) (ot : ∀ t ∈ R, ¬ Os0 t (Ts + ks))
    (lt : (Ts + ks).toNat < H0.toNat)
    (hwO : ∀ t ∈ R, ¬ Os0 t w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H0.toNat) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ MHS R Os0 H0 Nj M1 M G) (fun L M G => LP L ∧ MHS R Os0 H0 Nj M1 M G) RR
      (.call (some (none,none)) (ofString "htab_union_into")
        [.load .one (.op .add [.var .global (ofString "bs"),.const kb]),
         .load .one (.op .add [.var .global (ofString "ts"),.const ks])]) := by
  refine aqgd_conseqA (P' := fun L M G => ∃ q : (BitVec 64 × (BitVec 64 → BitVec 64 → Prop)) × (Mem × GA),
      (LP L ∧ M = q.2.1 ∧ G = q.2.2) ∧ ((HeapIs q.2.2 q.1.1 ∧ H0.toNat ≤ q.1.1.toNat ∧ BTF R q.1.2 q.1.1 q.2.1 ∧
        (∀ t x, q.1.2 t x → Os0 t x ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < q.1.1.toNat)) ∧
        q.2.2.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∀ x, (∀ t ∈ R, ¬ Os0 t x) → x.toNat < H0.toNat → q.2.1 x = M1 x) ∧
        q.2.2.lookup (ofString "bs") = some (.val (.word Bs)) ∧ q.2.2.lookup (ofString "ts") = some (.val (.word Ts))))
    (aqgd_ex (fun q => ?_)) ?_
  · rcases q with ⟨⟨H,Os⟩,M2,G2⟩
    refine aqgd_preP (fun ⟨⟨hH,le,f,gr,hn,fr⟩,gbs,gts⟩ => ?_)
    dsimp only at hH le f gr hn fr gbs gts
    have hwOj : ¬ Os j w := fun h => (gr j w h).elim (hwO j hj) (fun ⟨h1,_⟩ => by omega)
    have frB : M2 (Bs + kb) = M1 (Bs + kb) := fr _ ob lb
    have frT : M2 (Ts + ks) = M1 (Ts + ks) := fr _ ot lt
    refine aqgd_conseq (aqgd_call_unionO (LP := LP) _ _ (Os j) j H Nj M2 G2 (f.1 j hj) hH hn hwOj hwP (by omega) ?_)
      (fun L M G h => h) (fun L M G ⟨lp,u⟩ => ?_) (fun _ _ _ h => h)
    · intro F s sd sm sg lp
      exact ⟨y,union_record_args s .global .global _ _ Bs Ts kb ks j y
        (eval_global_word s _ Bs (by rw [sg]; exact gbs)) (eval_global_word s _ Ts (by rw [sg]; exact gts))
        (by rw [sd]; exact db) (by rw [sm,frB]; exact cb) (by rw [sd]; exact dt) (by rw [sm,frT]; exact ct)⟩
    · obtain ⟨H',hH',le',f',hn',fr'⟩ := btf_union hj f u
      refine ⟨lp,H',_,hH',by omega,f',fun t x h => ?_,hn',fun x hx hlt => ?_⟩
      · rcases h with h | ⟨_,h1,h2⟩
        · rcases gr t x h with h | ⟨h1,h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1,by omega⟩
        · exact Or.inr ⟨by omega,h2⟩
      · refine (fr' x (fun h => ?_) (by omega)).trans (fr x hx hlt)
        rcases gr j x h with h | ⟨h1,_⟩
        · exact hx j hj h
        · omega
  · intro L M G aw ⟨lp,H,Os,hH,le,f,gr,hn,fr⟩
    obtain ⟨ebs,_⟩ := aw.1.1.1.1.1.2.2.2 (ofString "bs") (by decide)
    obtain ⟨ets,_⟩ := aw.1.1.1.1.1.2.2.2 (ofString "ts") (by decide)
    exact ⟨((H,Os),(M,G)),⟨lp,rfl,rfl⟩,⟨hH,le,f,gr,hn,fr⟩,by rw [ebs]; exact hBs,by rw [ets]; exact hTs⟩

#print axioms aqgd_call_unionMH

/-- The head of `merge_tx_into_block`: the five unions `bs + k ← ts + k` (`k = 24, 8, 40, 16, 48`) into family members. -/
theorem mergeHeadF_aqgd {LP : GA → Prop} {Q : GA → Mem → GA → Prop} {cont : ProgHOL 64}
    (R : Set (BitVec 64)) (Os0 : BitVec 64 → BitVec 64 → Prop) (Bs Ts H0 Nj : BitVec 64) (M1 : Mem)
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (j24 y24 : BitVec 64) (hj24 : j24 ∈ R) (db24 : D (Bs + 24#64)) (cb24 : M1 (Bs + 24#64) = .word j24)
    (ob24 : ∀ t ∈ R, ¬ Os0 t (Bs + 24#64)) (lb24 : (Bs + 24#64).toNat < H0.toNat)
    (dt24 : D (Ts + 24#64)) (ct24 : M1 (Ts + 24#64) = .word y24) (ot24 : ∀ t ∈ R, ¬ Os0 t (Ts + 24#64))
    (lt24 : (Ts + 24#64).toNat < H0.toNat)
    (j8 y8 : BitVec 64) (hj8 : j8 ∈ R) (db8 : D (Bs + 8#64)) (cb8 : M1 (Bs + 8#64) = .word j8)
    (ob8 : ∀ t ∈ R, ¬ Os0 t (Bs + 8#64)) (lb8 : (Bs + 8#64).toNat < H0.toNat)
    (dt8 : D (Ts + 8#64)) (ct8 : M1 (Ts + 8#64) = .word y8) (ot8 : ∀ t ∈ R, ¬ Os0 t (Ts + 8#64))
    (lt8 : (Ts + 8#64).toNat < H0.toNat)
    (j40 y40 : BitVec 64) (hj40 : j40 ∈ R) (db40 : D (Bs + 40#64)) (cb40 : M1 (Bs + 40#64) = .word j40)
    (ob40 : ∀ t ∈ R, ¬ Os0 t (Bs + 40#64)) (lb40 : (Bs + 40#64).toNat < H0.toNat)
    (dt40 : D (Ts + 40#64)) (ct40 : M1 (Ts + 40#64) = .word y40) (ot40 : ∀ t ∈ R, ¬ Os0 t (Ts + 40#64))
    (lt40 : (Ts + 40#64).toNat < H0.toNat)
    (j16 y16 : BitVec 64) (hj16 : j16 ∈ R) (db16 : D (Bs + 16#64)) (cb16 : M1 (Bs + 16#64) = .word j16)
    (ob16 : ∀ t ∈ R, ¬ Os0 t (Bs + 16#64)) (lb16 : (Bs + 16#64).toNat < H0.toNat)
    (dt16 : D (Ts + 16#64)) (ct16 : M1 (Ts + 16#64) = .word y16) (ot16 : ∀ t ∈ R, ¬ Os0 t (Ts + 16#64))
    (lt16 : (Ts + 16#64).toNat < H0.toNat)
    (j48 y48 : BitVec 64) (hj48 : j48 ∈ R) (db48 : D (Bs + 48#64)) (cb48 : M1 (Bs + 48#64) = .word j48)
    (ob48 : ∀ t ∈ R, ¬ Os0 t (Bs + 48#64)) (lb48 : (Bs + 48#64).toNat < H0.toNat)
    (dt48 : D (Ts + 48#64)) (ct48 : M1 (Ts + 48#64) = .word y48) (ot48 : ∀ t ∈ R, ¬ Os0 t (Ts + 48#64))
    (lt48 : (Ts + 48#64).toNat < H0.toNat)
    (hwO : ∀ t ∈ R, ¬ Os0 t w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H0.toNat)
    (hcont : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ MHS R Os0 H0 Nj M1 M G) Q RR cont) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ MHS R Os0 H0 Nj M1 M G) Q RR
      (.seq (.call (some (none,none)) (ofString "htab_union_into")
        [.load .one (.op .add [.var .global (ofString "bs"),.const 24#64]),
         .load .one (.op .add [.var .global (ofString "ts"),.const 24#64])])
        (.seq (.call (some (none,none)) (ofString "htab_union_into")
        [.load .one (.op .add [.var .global (ofString "bs"),.const 8#64]),
         .load .one (.op .add [.var .global (ofString "ts"),.const 8#64])])
        (.seq (.call (some (none,none)) (ofString "htab_union_into")
        [.load .one (.op .add [.var .global (ofString "bs"),.const 40#64]),
         .load .one (.op .add [.var .global (ofString "ts"),.const 40#64])])
        (.seq (.call (some (none,none)) (ofString "htab_union_into")
        [.load .one (.op .add [.var .global (ofString "bs"),.const 16#64]),
         .load .one (.op .add [.var .global (ofString "ts"),.const 16#64])])
        (.seq (.call (some (none,none)) (ofString "htab_union_into")
        [.load .one (.op .add [.var .global (ofString "bs"),.const 48#64]),
         .load .one (.op .add [.var .global (ofString "ts"),.const 48#64])])
        cont))))) :=
  (aqgd_seq (aqgd_call_unionMH R Os0 j24 24#64 24#64 Bs Ts H0 Nj y24 M1 hj24 hBs hTs db24 cb24 ob24 lb24 dt24 ct24 ot24 lt24
      hwO hwP p0) (aqgd_seq (aqgd_call_unionMH R Os0 j8 8#64 8#64 Bs Ts H0 Nj y8 M1 hj8 hBs hTs db8 cb8 ob8 lb8 dt8 ct8 ot8 lt8
      hwO hwP p0) (aqgd_seq (aqgd_call_unionMH R Os0 j40 40#64 40#64 Bs Ts H0 Nj y40 M1 hj40 hBs hTs db40 cb40 ob40 lb40 dt40 ct40 ot40 lt40
      hwO hwP p0) (aqgd_seq (aqgd_call_unionMH R Os0 j16 16#64 16#64 Bs Ts H0 Nj y16 M1 hj16 hBs hTs db16 cb16 ob16 lb16 dt16 ct16 ot16 lt16
      hwO hwP p0) (aqgd_seq (aqgd_call_unionMH R Os0 j48 48#64 48#64 Bs Ts H0 Nj y48 M1 hj48 hBs hTs db48 cb48 ob48 lb48 dt48 ct48 ot48 lt48
      hwO hwP p0) hcont)))))

#print axioms mergeHeadF_aqgd
end mu
end InitECandidate.Runtime
