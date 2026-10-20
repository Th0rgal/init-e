import InitECandidate.Runtime.RecKeccakGD
/-!
Struct stores: a store of a value flattening to `k` words touches only `a + 8 j`, `j < k` (`aqgd_storeK`);
four-word values (`U4V`) from their shape.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A sequence of word stores only touches `a, a + 8, ...`. -/
theorem panMemStores_frame (ws : List (HolWordLab 64)) : ∀ (a : BitVec 64) (dom : BitVec 64 → Prop) [DecidablePred dom]
    (m m' : BitVec 64 → HolWordLab 64) (x : BitVec 64), panMemStoresHOL a ws dom m = some m' →
    (∀ j : Nat, j < ws.length → x ≠ a + BitVec.ofNat 64 (8 * j)) → m' x = m x := by
  induction ws with
  | nil => intro a dom _ m m' x h _; simp [panMemStoresHOL] at h; rw [h]
  | cons v rest ih =>
    intro a dom _ m m' x h out
    simp only [panMemStoresHOL] at h
    split at h
    · rename_i upd hupd
      have r := ih (a + panBytesInWord 64) dom upd m' x h (fun j hj e => out (j + 1) (by simp; omega) (by
        rw [e]; simp [panBytesInWord,BitVec.add_assoc]
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega))
      rw [r]
      simp only [panMemStoreHOL] at hupd
      split at hupd
      · simp only [Option.some.injEq] at hupd
        rw [← hupd]
        have : x ≠ a := fun e => out 0 (by simp) (by rw [e]; simp)
        simp [this]
      · cases hupd
    · cases h

#print axioms panMemStores_frame

/-- A store of a value flattening to `k` words keeps every word other than `a + 8 j`, `j < k`. -/
theorem evaluate_store_frameK {F : Type} (s : PanSemStateFiniteExact 64 F) (d v : ExpHOL 64) (a : BitVec 64) (k : Nat)
    (hd : EV s d = some (.val (.word a))) (hv : ∀ x, EV s v = some x → (flattenHOL x).length = k) :
    ((evaluateHOLFiniteState s (.store d v)).1 = none ∨ (evaluateHOLFiniteState s (.store d v)).1 = some .error) ∧
      (evaluateHOLFiniteState s (.store d v)).2.locals = s.locals ∧
      (evaluateHOLFiniteState s (.store d v)).2.globals = s.globals ∧
      (∀ x : BitVec 64, (∀ j : Nat, j < k → x ≠ a + BitVec.ofNat 64 (8 * j)) →
        (evaluateHOLFiniteState s (.store d v)).2.memory x = s.memory x) := by
  rw [evaluateHOLFiniteState_store]
  simp only [EV] at hd hv
  rw [hd]
  dsimp only
  split
  · rename_i x hx
    have hl := hv x hx
    split
    · rename_i m hm
      exact ⟨Or.inl rfl,rfl,rfl,fun y out => @panMemStores_frame _ a s.memaddrs (fun z => Classical.propDecidable (s.memaddrs z)) _ _ y hm (by rw [hl]; exact out)⟩
    · exact ⟨Or.inr rfl,rfl,rfl,fun _ _ => rfl⟩
  · exact ⟨Or.inr rfl,rfl,rfl,fun _ _ => rfl⟩

#print axioms evaluate_store_frameK

/-- A four-word value. -/
def U4V (v : ValueHOL 64) : Prop :=
  ∃ a b c d : BitVec 64, v = .rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]

theorem u4v_len {v : ValueHOL 64} (h : U4V v) : (flattenHOL v).length = 4 := by
  obtain ⟨a,b,c,d,rfl⟩ := h
  simp [flattenHOL]

theorem word_of_shape_one {v : ValueHOL 64} (h : shapeOfHOLExact v = .one) : ∃ y : BitVec 64, v = .val (.word y) := by
  cases v with
  | val x => cases x with | word y => exact ⟨y,rfl⟩
  | rStruct fs => simp [shapeOfHOLExact] at h
  | nStruct n fs => simp [shapeOfHOLExact] at h

theorem u4v_of_shape {v : ValueHOL 64} (h : shapeOfHOLExact v = .comb [.one,.one,.one,.one]) : U4V v := by
  cases v with
  | val x => simp [shapeOfHOLExact] at h
  | nStruct n fs => simp [shapeOfHOLExact] at h
  | rStruct fs =>
    simp [shapeOfHOLExact] at h
    rcases fs with _ | ⟨v1,_ | ⟨v2,_ | ⟨v3,_ | ⟨v4,_ | ⟨v5,fs⟩⟩⟩⟩⟩ <;> simp at h
    obtain ⟨h1,h2,h3,h4⟩ := h
    obtain ⟨a,rfl⟩ := word_of_shape_one h1
    obtain ⟨b,rfl⟩ := word_of_shape_one h2
    obtain ⟨c,rfl⟩ := word_of_shape_one h3
    obtain ⟨d,rfl⟩ := word_of_shape_one h4
    exact ⟨a,b,c,d,rfl⟩

#print axioms u4v_of_shape

section sk
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A store of a `k`-word value whose words avoid the watched word. -/
theorem aqgd_storeK {LP LQ : GA → GA → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals → LP s.locals s.globals →
      ∃ (a : BitVec 64) (k : Nat), EV s d = some (.val (.word a)) ∧
        (∀ x, EV s v = some x → (flattenHOL x).length = k) ∧
        (∀ j : Nat, j < k → w ≠ a + BitVec.ofNat 64 (8 * j)) ∧ LQ s.locals s.globals) :
    AQGD D B A w Vn (fun L _ G => LP L G) (fun L _ G => LQ L G) RR (.store d v) := by
  intro F s code dom aw sl G hG pre
  unfold GIs at hG; subst hG
  obtain ⟨a,k,ha,hk,out,lq⟩ := hd s aw pre
  obtain ⟨res,loc,glob,mem⟩ := evaluate_store_frameK s d v a k ha hk
  refine ⟨mem w out,fun _ => by rw [glob]; exact aw,fun _ => ⟨by rw [loc]; exact sl,_,by rw [glob]; rfl,by
      rw [loc]; exact lq⟩,?_,?_,?_⟩
  · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
  all_goals rcases res with h | h <;> rw [h] <;> simp

#print axioms aqgd_storeK
end sk
end InitECandidate.Runtime
