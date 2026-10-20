import InitECandidate.Runtime.PtSegBaseGD
/-!
Fenced stores of values of any shape: a successful store of a value flattening to `k` words has every word address
`a + 8 j` in the domain, so under the fence `D ⊆ [0, DF)` with `DF + 8 ≤ 2^64` from `a` the addresses never wrap; a
failing store changes nothing. Hence a store at or above `Lo` keeps the segment state `SI` whatever the stored value.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful sequence of word stores has every address in the domain. -/
theorem panMemStores_dom (ws : List (HolWordLab 64)) : ∀ (a : BitVec 64) (dom : BitVec 64 → Prop) [DecidablePred dom]
    (m m' : BitVec 64 → HolWordLab 64), panMemStoresHOL a ws dom m = some m' →
    ∀ j : Nat, j < ws.length → dom (a + BitVec.ofNat 64 (8 * j)) := by
  induction ws with
  | nil => intro a dom _ m m' _ j hj; simp at hj
  | cons v rest ih =>
    intro a dom _ m m' h j hj
    simp only [panMemStoresHOL] at h
    split at h
    · rename_i upd hupd
      cases j with
      | zero =>
        simp only [panMemStoreHOL] at hupd
        split at hupd
        · rename_i hd
          simpa using hd
        · cases hupd
      | succ j =>
        have r := ih (a + panBytesInWord 64) dom upd m' h j (by simp at hj; omega)
        have e : a + panBytesInWord 64 + BitVec.ofNat 64 (8 * j) = a + BitVec.ofNat 64 (8 * (j + 1)) := by
          simp [panBytesInWord,BitVec.add_assoc]
          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
        rw [← e]; exact r
    · cases h

#print axioms panMemStores_dom

/-- A store either fails with nothing changed, or succeeds with every word address in the domain and only those
addresses changed. -/
theorem evaluate_store_any {F : Type} (s : PanSemStateFiniteExact 64 F) (d v : ExpHOL 64) (a : BitVec 64)
    (hd : EV s d = some (.val (.word a))) :
    (evaluateHOLFiniteState s (.store d v)).2.locals = s.locals ∧
      (evaluateHOLFiniteState s (.store d v)).2.globals = s.globals ∧
      (((evaluateHOLFiniteState s (.store d v)).1 = some .error ∧
        (evaluateHOLFiniteState s (.store d v)).2.memory = s.memory) ∨
      ((evaluateHOLFiniteState s (.store d v)).1 = none ∧ ∃ x, EV s v = some x ∧
        (∀ j : Nat, j < (flattenHOL x).length → s.memaddrs (a + BitVec.ofNat 64 (8 * j))) ∧
        ∀ y : BitVec 64, (∀ j : Nat, j < (flattenHOL x).length → y ≠ a + BitVec.ofNat 64 (8 * j)) →
          (evaluateHOLFiniteState s (.store d v)).2.memory y = s.memory y)) := by
  rw [evaluateHOLFiniteState_store]
  simp only [EV] at hd ⊢
  rw [hd]
  dsimp only
  split
  · rename_i x hx
    split
    · rename_i m hm
      exact ⟨rfl,rfl,Or.inr ⟨rfl,x,hx,
        fun j hj => @panMemStores_dom _ a s.memaddrs (fun z => Classical.propDecidable (s.memaddrs z)) _ _ hm j hj,
        fun y out => @panMemStores_frame _ a s.memaddrs (fun z => Classical.propDecidable (s.memaddrs z)) _ _ y hm out⟩⟩
    · exact ⟨rfl,rfl,Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨rfl,rfl,Or.inl ⟨rfl,rfl⟩⟩

#print axioms evaluate_store_any

/-- Under the fence, word addresses `a + 8 j` all in the domain do not wrap and lie below `DF`. -/
theorem fence_nowrap {D : BitVec 64 → Prop} {DF : Nat} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 64) (a : BitVec 64)
    (k : Nat) (hdom : ∀ j : Nat, j < k → D (a + BitVec.ofNat 64 (8 * j))) :
    ∀ j : Nat, j < k → (a + BitVec.ofNat 64 (8 * j)).toNat = a.toNat + 8 * j ∧ a.toNat + 8 * j < DF := by
  intro j
  induction j with
  | zero =>
    intro hk
    have e : a + BitVec.ofNat 64 (8 * 0) = a := by simp
    have := hF _ (hdom 0 hk)
    rw [e] at this ⊢
    exact ⟨rfl,by omega⟩
  | succ j ih =>
    intro hk
    obtain ⟨_,lt⟩ := ih (by omega)
    have e : (a + BitVec.ofNat 64 (8 * (j + 1))).toNat = a.toNat + 8 * (j + 1) := by
      simp [BitVec.toNat_add]; omega
    have := hF _ (hdom (j + 1) hk)
    rw [e] at this ⊢
    exact ⟨rfl,this⟩

#print axioms fence_nowrap

section sa
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {Lo Nj : BitVec 64} {M0 : Mem}

/-- A store of any value at an address at or above `Lo` keeps `SI` (fenced domain). -/
theorem aqgd_storeAny_si {LP LQ : GA → Prop} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 64) (hw : w.toNat < Lo.toNat)
    (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals → LP s.locals →
      ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ Lo.toNat ≤ a.toNat ∧ LQ s.locals) :
    AQGD D B A w Vn (fun L M G => LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
      (fun L M G => LQ L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) RR (.store d v) := by
  intro F s code dom aw sl G hG ⟨lp,si⟩
  unfold GIs at hG; subst hG
  obtain ⟨a,ha,hlo,lq⟩ := hd s aw lp
  obtain ⟨loc,glob,res⟩ := evaluate_store_any s d v a ha
  rcases res with ⟨e,hm⟩ | ⟨e,x,_,hdom,fr⟩
  · refine ⟨by rw [hm],fun c => ?_,fun e' => ?_,fun v' e' => ?_,by rw [e]; simp,by rw [e]; simp⟩
    · rcases c with c | c | c | ⟨_,c⟩ <;> rw [e] at c <;> cases c
    · rw [e] at e'; cases e'
    · rw [e] at e'; cases e'
  · have hk : ∀ j : Nat, j < (flattenHOL x).length → D (a + BitVec.ofNat 64 (8 * j)) :=
      fun j hj => dom.2.1 ▸ hdom j hj
    have nw := fence_nowrap hF hDF a _ hk
    have keep : ∀ y : BitVec 64, y.toNat < Lo.toNat →
        (evaluateHOLFiniteState s (.store d v)).2.memory y = s.memory y := by
      intro y hy
      refine fr y (fun j hj ey => ?_)
      have := (nw j hj).1
      rw [← ey] at this; omega
    refine ⟨keep w hw,fun _ => by rw [glob]; exact aw,fun _ => ⟨by rw [loc]; exact sl,_,by unfold GIs; rw [glob],?_⟩,
      (fun v' e' => by rw [e] at e'; cases e'),by rw [e]; simp,by rw [e]; simp⟩
    rw [loc]
    exact ⟨lq,si_mem si keep⟩

#print axioms aqgd_storeAny_si
end sa
end InitECandidate.Runtime
