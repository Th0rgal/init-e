import InitECandidate.Runtime.HtabSpecArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Word-valued locals, listed by name. -/
def LK (pairs : List (MlS × BitVec 64)) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∀ p ∈ pairs, L.lookup p.1 = some (.val (.word p.2))

theorem lk_update {pairs : List (MlS × BitVec 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : LK pairs L)
    (x : MlS) (v : ValueHOL 64) (hx : ∀ p ∈ pairs, p.1 ≠ x) : LK pairs (L.update (x,v)) := by
  intro p hp
  simp [HolFiniteMapExact.lookup_update,FUPDATE,h p hp]
  exact fun e => absurd e.symm (hx p hp)

theorem lk_res {pairs : List (MlS × BitVec 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : LK pairs L)
    (x : MlS) (o : Option (ValueHOL 64)) (hx : ∀ p ∈ pairs, p.1 ≠ x) : LK pairs (L.resVarEq (x,o)) := by
  intro p hp
  rw [resVar_lookup_ne L x p.1 o (hx p hp)]
  exact h p hp

theorem lk_cons {pairs : List (MlS × BitVec 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : LK pairs L)
    (x : MlS) (y : BitVec 64) (hx : ∀ p ∈ pairs, p.1 ≠ x) : LK ((x,y) :: pairs) (L.update (x,.val (.word y))) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp [HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [HolFiniteMapExact.lookup_update,FUPDATE,h p hp]
    exact fun e => absurd e.symm (hx p hp)

theorem lk_get {pairs : List (MlS × BitVec 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : LK pairs L)
    (x : MlS) (y : BitVec 64) (hx : (x,y) ∈ pairs) : L.lookup x = some (.val (.word y)) := h _ hx

/-- Table header cells at `T`. -/
def Hdr (M : Mem) (T KL SD C N KS VS US OS OPS : BitVec 64) : Prop :=
  M (T + 0#64) = .word KL ∧ M (T + 8#64) = .word SD ∧ M (T + 16#64) = .word C ∧ M (T + 24#64) = .word N ∧
    M (T + 32#64) = .word KS ∧ M (T + 40#64) = .word VS ∧ M (T + 48#64) = .word US ∧ M (T + 56#64) = .word OS ∧
    M (T + 64#64) = .word OPS

/-- An array of `len` bytes lies in the table body `[T + 72, E)` or in fresh heap `[P0, HEAP_END]`. -/
def Arr (P0 T E a : BitVec 64) (len : Nat) : Prop :=
  (T.toNat + 72 ≤ a.toNat ∧ a.toNat + len ≤ E.toNat) ∨ (P0.toNat ≤ a.toNat ∧ a.toNat + len ≤ 33806089496)

/-- Table footprint: the table region `[T, E)` or fresh heap. -/
def Foot (P0 T E x : BitVec 64) : Prop := (T.toNat ≤ x.toNat ∧ x.toNat < E.toNat) ∨ P0.toNat ≤ x.toNat

/-- The header layout: power-of-two capacity, aligned keys/stride/used, `count < cap`, arrays inside the table
region or fresh heap, header below the arrays and below fresh heap. -/
structure HLay (P0 T E KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat) : Prop where
  pow : C.toNat = 2 ^ b
  fits : KL.toNat ≤ SD.toNat
  sdAl : SD.toNat % 8 = 0
  ksAl : KS.toNat % 8 = 0
  usAl : US.toNat % 8 = 0
  cnt : N.toNat < C.toNat
  hdr : T.toNat + 72 ≤ E.toNat
  hdrP : T.toNat + 72 ≤ P0.toNat
  eEnd : E.toNat ≤ 33806089496
  keysR : Arr P0 T E KS (C.toNat * SD.toNat)
  valsR : Arr P0 T E VS (C.toNat * 8)
  usedR : Arr P0 T E US C.toNat
  orderR : Arr P0 T E OS (C.toNat * 8)
  oposR : Arr P0 T E OPS (C.toNat * 8)

theorem arr_foot {P0 T E a : BitVec 64} {len : Nat} (h : Arr P0 T E a len) (x : BitVec 64)
    (lo : a.toNat ≤ x.toNat) (hi : x.toNat < a.toNat + len) : Foot P0 T E x := by
  rcases h with ⟨h1,h2⟩ | ⟨h1,_⟩
  · exact Or.inl ⟨by omega,by omega⟩
  · exact Or.inr (by omega)

theorem arr_end {P0 T E a : BitVec 64} {len : Nat} (h : Arr P0 T E a len) (eE : E.toNat ≤ 33806089496) :
    a.toNat + len ≤ 33806089496 := by
  rcases h with ⟨_,h2⟩ | ⟨_,h2⟩ <;> omega

theorem arr_hdr {P0 T E a : BitVec 64} {len : Nat} (h : Arr P0 T E a len) (hP : T.toNat + 72 ≤ P0.toNat) :
    T.toNat + 72 ≤ a.toNat := by
  rcases h with ⟨h1,_⟩ | ⟨h1,_⟩ <;> omega

theorem ev_load_off {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (X off : BitVec 64) (v : ValueHOL 64)
    (hx : s.locals.lookup x = some (.val (.word X)))
    (ev : EV s (.load .one (.op .add [.var .local x,.const off])) = some v) : v = .val (s.memory (X + off)) := by
  simp [EV,evalHOLExact,evalListHOLExact,hx,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact] at ev
  exact ev.2.symm

theorem mask_lt (h C : BitVec 64) (b : Nat) (pow : C.toNat = 2 ^ b) (small : C.toNat ≤ 33806089496) :
    (h &&& (C - 1#64)).toNat < C.toNat := by
  have hc : 1 ≤ C.toNat := by rw [pow]; exact Nat.one_le_two_pow
  have e : (C - 1#64).toNat = C.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simp; omega))]; simp
  rw [BitVec.toNat_and,e]
  have := Nat.and_le_right (n := h.toNat) (m := C.toNat - 1)
  omega

theorem mask_lt' (h C : BitVec 64) (b : Nat) (pow : C.toNat = 2 ^ b) (small : C.toNat ≤ 33806089496) :
    (h &&& ((C - 1#64) &&& 18446744073709551615#64)).toNat < C.toNat := by
  have e : (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 := by decide
  rw [e,BitVec.and_allOnes]
  exact mask_lt h C b pow small

/-- Writes that miss the header keep the header cells. -/
theorem hdr_keep {M M' : Mem} {T KL SD C N KS VS US OS OPS : BitVec 64} (h : Hdr M T KL SD C N KS VS US OS OPS)
    (fit : T.toNat + 72 < 2 ^ 64)
    (keep : ∀ x : BitVec 64, T.toNat ≤ x.toNat → x.toNat < T.toNat + 72 → M' x = M x) :
    Hdr M' T KL SD C N KS VS US OS OPS := by
  have c : ∀ k : BitVec 64, k.toNat < 72 → M' (T + k) = M (T + k) := fun k hk => by
    apply keep
    · rw [BitVec.toNat_add_of_lt (by omega)]; omega
    · rw [BitVec.toNat_add_of_lt (by omega)]; omega
  obtain ⟨h0,h8,h16,h24,h32,h40,h48,h56,h64⟩ := h
  exact ⟨(c _ (by decide)).trans h0,(c _ (by decide)).trans h8,(c _ (by decide)).trans h16,
    (c _ (by decide)).trans h24,(c _ (by decide)).trans h32,(c _ (by decide)).trans h40,(c _ (by decide)).trans h48,
    (c _ (by decide)).trans h56,(c _ (by decide)).trans h64⟩

theorem word_update_keep {M : Mem} {a : BitVec 64} {y : BitVec 64} (x : BitVec 64) (ne : x ≠ a) :
    (fun z => if z = a then HolWordLab.word y else M z) x = M x := by simp [ne]

theorem toNat_add_small (A k : BitVec 64) (h : A.toNat + k.toNat < 2 ^ 64) : (A + k).toNat = A.toNat + k.toNat := by
  rw [BitVec.toNat_add_of_lt h]

theorem toNat_add_mul8 (A i : BitVec 64) (h : A.toNat + i.toNat * 8 < 2 ^ 64) :
    (A + i * 8#64).toNat = A.toNat + i.toNat * 8 := by
  have h8 : (8#64).toNat = 8 := rfl
  have hm : (i * 8#64).toNat = i.toNat * 8 := by
    rw [BitVec.toNat_mul,h8]; exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add_of_lt (by omega),hm]

theorem toNat_add_mul (A i S : BitVec 64) (h : A.toNat + i.toNat * S.toNat < 2 ^ 64) :
    (A + i * S).toNat = A.toNat + i.toNat * S.toNat := by
  have hm : (i * S).toNat = i.toNat * S.toNat := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add_of_lt (by omega),hm]

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → Prop}

/-- A word store whose address facts are only needed when the address evaluates to a word. -/
theorem aqm_store' {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (a : BitVec 64), AW SP0 P0 FM G0 s.globals →
      P s.locals s.memory → SL Vn s.locals → EV s d = some (.val (.word a)) → w ≠ a ∧
        ∀ y : BitVec 64, EV s v = some (.val (.word y)) → Q s.locals (fun x => if x = a then .word y else s.memory x))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, AW SP0 P0 FM G0 s.globals → P s.locals s.memory →
      SL Vn s.locals → EV s v = some x → ∃ y : BitVec 64, x = .val (.word y)) :
    AQM SP0 P0 FM G0 w Vn P Q RR (.store d v) := by
  intro F s code dom aw sl pre
  cases hda : EV s d with
  | none =>
    have e : evaluateHOLFiniteState s (.store d v) = (some .error,s) := by
      rw [evaluateHOLFiniteState_store]; simp only [EV] at hda; rw [hda]
    rw [e]; exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some x =>
    rcases x with ⟨⟨a⟩⟩ | fs | ⟨n,fs⟩
    · obtain ⟨ne,hq⟩ := hd s a aw pre sl hda
      obtain ⟨res,_,loc,glob,mem⟩ := evaluate_store_word_frame s d v a hda (hv s · aw pre sl)
      refine ⟨mem w ne,fun _ => by rw [glob]; exact aw,fun e => ⟨by rw [loc]; exact sl,?_⟩,?_,?_,?_⟩
      · cases hvv : EV s v with
        | none =>
          exfalso
          rw [evaluateHOLFiniteState_store] at e
          simp only [EV] at hda hvv
          rw [hda] at e
          dsimp only at e
          rw [hvv] at e
          cases e
        | some x =>
          obtain ⟨y,rfl⟩ := hv s x aw pre sl hvv
          rw [loc,store_none_mem s d v a y hda hvv e]
          exact hq y hvv
      · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
      all_goals rcases res with h | h <;> rw [h] <;> simp
    all_goals
      have e : evaluateHOLFiniteState s (.store d v) = (some .error,s) := by
        rw [evaluateHOLFiniteState_store]; simp only [EV] at hda; rw [hda]
      rw [e]; exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- A byte store whose address facts are only needed when the address evaluates to a word. -/
theorem aqm_storeByte' {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (a : BitVec 64), AW SP0 P0 FM G0 s.globals →
      P s.locals s.memory → SL Vn s.locals → EV s d = some (.val (.word a)) → w ≠ panByteAlignHOL a ∧
        ∀ M' : Mem, (∀ x, x ≠ panByteAlignHOL a → M' x = s.memory x) → Q s.locals M') :
    AQM SP0 P0 FM G0 w Vn P Q RR (.storeByte d v) := by
  intro F s code dom aw sl pre
  cases hda : EV s d with
  | none =>
    have e : evaluateHOLFiniteState s (.storeByte d v) = (some .error,s) := by
      rw [evaluateHOLFiniteState_storeByte]; simp only [EV] at hda; rw [hda]
    rw [e]; exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some x =>
    rcases x with ⟨⟨a⟩⟩ | fs | ⟨n,fs⟩
    · obtain ⟨ne,hq⟩ := hd s a aw pre sl hda
      obtain ⟨res,_,loc,glob,_,_,_⟩ := evaluate_storeByte_control_frame s d v
      refine ⟨evaluate_storeByte_memory_frame s d v a w hda ne,fun _ => by rw [glob]; exact aw,
        fun _ => ⟨by rw [loc]; exact sl,by rw [loc]; exact hq _ (fun x hx => evaluate_storeByte_memory_frame s d v a x hda hx)⟩,
        ?_,?_,?_⟩
      · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
      all_goals rcases res with h | h <;> rw [h] <;> simp
    all_goals
      have e : evaluateHOLFiniteState s (.storeByte d v) = (some .error,s) := by
        rw [evaluateHOLFiniteState_storeByte]; simp only [EV] at hda; rw [hda]
      rw [e]; exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- Table memory invariant: header cells and agreement with the entry memory outside the footprint. -/
def MI (P0 T E : BitVec 64) (M0 : Mem) (KL SD C N KS VS US OS OPS : BitVec 64) (M : Mem) : Prop :=
  Hdr M T KL SD C N KS VS US OS OPS ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x

theorem mi_write {P0 T E : BitVec 64} {M0 M M' : Mem} {KL SD C N KS VS US OS OPS : BitVec 64}
    (h : MI P0 T E M0 KL SD C N KS VS US OS OPS M) (fit : T.toNat + 72 < 2 ^ 64) (a : BitVec 64)
    (ha : Foot P0 T E a) (hout : T.toNat + 72 ≤ a.toNat) (hM' : ∀ x, x ≠ a → M' x = M x) :
    MI P0 T E M0 KL SD C N KS VS US OS OPS M' := by
  refine ⟨hdr_keep h.1 fit (fun x lo hi => hM' x (fun e => by subst e; omega)),fun x hx => ?_⟩
  rw [hM' x (fun e => by subst e; exact hx ha)]
  exact h.2 x hx

theorem mi_count {P0 T E : BitVec 64} {M0 M : Mem} {KL SD C N KS VS US OS OPS : BitVec 64}
    (h : MI P0 T E M0 KL SD C N KS VS US OS OPS M) (fit : T.toNat + 72 ≤ E.toNat) (hE : E.toNat < 2 ^ 64) :
    MI P0 T E M0 KL SD C (N + 1#64) KS VS US OS OPS
      (fun x => if x = T + 24#64 then .word (N + 1#64) else M x) := by
  obtain ⟨⟨h0,h8,h16,h24,h32,h40,h48,h56,h64⟩,ag⟩ := h
  have ne : ∀ k : BitVec 64, k.toNat < 72 → k ≠ 24#64 → T + k ≠ T + 24#64 := fun k _ hk e =>
    hk (add_left_cancel e)
  constructor
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · show (if T + 0#64 = T + 24#64 then HolWordLab.word (N + 1#64) else M (T + 0#64)) = _
      rw [if_neg (ne _ (by decide) (by decide))]; exact h0
    · show (if T + 8#64 = T + 24#64 then HolWordLab.word (N + 1#64) else M (T + 8#64)) = _
      rw [if_neg (ne _ (by decide) (by decide))]; exact h8
    · show (if T + 16#64 = T + 24#64 then HolWordLab.word (N + 1#64) else M (T + 16#64)) = _
      rw [if_neg (ne _ (by decide) (by decide))]; exact h16
    · show (if T + 24#64 = T + 24#64 then HolWordLab.word (N + 1#64) else M (T + 24#64)) = _
      rw [if_pos rfl]
    · show (if T + 32#64 = T + 24#64 then HolWordLab.word (N + 1#64) else M (T + 32#64)) = _
      rw [if_neg (ne _ (by decide) (by decide))]; exact h32
    · show (if T + 40#64 = T + 24#64 then HolWordLab.word (N + 1#64) else M (T + 40#64)) = _
      rw [if_neg (ne _ (by decide) (by decide))]; exact h40
    · show (if T + 48#64 = T + 24#64 then HolWordLab.word (N + 1#64) else M (T + 48#64)) = _
      rw [if_neg (ne _ (by decide) (by decide))]; exact h48
    · show (if T + 56#64 = T + 24#64 then HolWordLab.word (N + 1#64) else M (T + 56#64)) = _
      rw [if_neg (ne _ (by decide) (by decide))]; exact h56
    · show (if T + 64#64 = T + 24#64 then HolWordLab.word (N + 1#64) else M (T + 64#64)) = _
      rw [if_neg (ne _ (by decide) (by decide))]; exact h64
  · intro x hx
    dsimp only
    have : x ≠ T + 24#64 := by
      intro e; subst e; apply hx; left
      rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega
    rw [if_neg this]; exact ag x hx

theorem mi_frame {P0 T E : BitVec 64} {M0 M M' : Mem} {KL SD C N KS VS US OS OPS : BitVec 64}
    (h : MI P0 T E M0 KL SD C N KS VS US OS OPS M) (fit : T.toNat + 72 < 2 ^ 64) (Win : BitVec 64 → Prop)
    (hwin : ∀ x, Win x → Foot P0 T E x ∧ T.toNat + 72 ≤ x.toNat) (hM' : ∀ x, ¬ Win x → M' x = M x) :
    MI P0 T E M0 KL SD C N KS VS US OS OPS M' := by
  refine ⟨hdr_keep h.1 fit (fun x lo hi => hM' x (fun hx => by have := (hwin x hx).2; omega)),fun x hx => ?_⟩
  rw [hM' x (fun hw => hx (hwin x hw).1)]
  exact h.2 x hx

/-- The `memcpy` byte window of slot `I`'s key lies in the keys array. -/
theorem keys_window {P0 T E KL SD C N KS VS US OS OPS : BitVec 64} {b : Nat}
    (lay : HLay P0 T E KL SD C N KS VS US OS OPS b) (I : BitVec 64) (hI : I.toNat < C.toNat) (x : BitVec 64)
    (hx : MWin (KS + I * SD) KL.toNat x) : Foot P0 T E x ∧ T.toNat + 72 ≤ x.toNat := by
  obtain ⟨j,hj,h | h⟩ := hx
  all_goals
    have kend := arr_end lay.keysR lay.eEnd
    have khdr := arr_hdr lay.keysR lay.hdrP
    have fits := lay.fits
    have mono : I.toNat * SD.toNat + SD.toNat ≤ C.toNat * SD.toNat := by
      have := Nat.mul_le_mul_right SD.toNat (Nat.succ_le_of_lt hI); rw [Nat.succ_mul] at this; exact this
    have eD : (KS + I * SD).toNat = KS.toNat + I.toNat * SD.toNat := toNat_add_mul KS I SD (by omega)
    have eDj : (KS + I * SD + BitVec.ofNat 64 j).toNat = KS.toNat + I.toNat * SD.toNat + j := by
      rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
  · subst h
    exact ⟨arr_foot lay.keysR _ (by omega) (by omega),by omega⟩
  · have e2 := panByteAlign_toNat64 (KS + I * SD + BitVec.ofNat 64 j)
    rw [eDj] at e2
    have al : (KS.toNat + I.toNat * SD.toNat) % 8 = 0 := by
      have := lay.ksAl; have := lay.sdAl
      rw [Nat.add_mod,Nat.mul_mod]; simp [*]
    have lo : KS.toNat + I.toNat * SD.toNat ≤ (KS.toNat + I.toNat * SD.toNat + j) / 8 * 8 := by
      have := Nat.div_add_mod (KS.toNat + I.toNat * SD.toNat) 8
      have := Nat.div_le_div_right (c := 8) (Nat.le_add_right (KS.toNat + I.toNat * SD.toNat) j)
      omega
    have hi := Nat.div_mul_le_self (KS.toNat + I.toNat * SD.toNat + j) 8
    rw [h]
    exact ⟨arr_foot lay.keysR _ (by omega) (by omega),by omega⟩

/-- Word slot `I < C` of an 8-byte array lies in the footprint, after the header. -/
theorem arr_slot8 {P0 T E A C I : BitVec 64} (h : Arr P0 T E A (C.toNat * 8)) (eE : E.toNat ≤ 33806089496)
    (hP : T.toNat + 72 ≤ P0.toNat) (hI : I.toNat < C.toNat) :
    Foot P0 T E (A + I * 8#64) ∧ T.toNat + 72 ≤ (A + I * 8#64).toNat := by
  have ae := arr_end h eE
  have ah := arr_hdr h hP
  have e := toNat_add_mul8 A I (by omega)
  exact ⟨arr_foot h _ (by omega) (by omega),by omega⟩

/-- The aligned word of byte `I < C` of an 8-aligned byte array lies in the footprint, after the header. -/
theorem arr_byte {P0 T E A C I : BitVec 64} (h : Arr P0 T E A C.toNat) (eE : E.toNat ≤ 33806089496)
    (hP : T.toNat + 72 ≤ P0.toNat) (al : A.toNat % 8 = 0) (hI : I.toNat < C.toNat) :
    Foot P0 T E (panByteAlignHOL (A + I)) ∧ T.toNat + 72 ≤ (panByteAlignHOL (A + I)).toNat := by
  have ae := arr_end h eE
  have ah := arr_hdr h hP
  have e1 : (A + I).toNat = A.toNat + I.toNat := by rw [BitVec.toNat_add_of_lt (by omega)]
  have e2 := panByteAlign_toNat64 (A + I)
  rw [e1] at e2
  have lo : A.toNat ≤ (A.toNat + I.toNat) / 8 * 8 := by
    have := Nat.div_add_mod A.toNat 8
    have := Nat.div_le_div_right (c := 8) (Nat.le_add_right A.toNat I.toNat)
    omega
  have hi := Nat.div_mul_le_self (A.toNat + I.toNat) 8
  exact ⟨arr_foot h _ (by omega) (by omega),by omega⟩

macro "lkne" : tactic => `(tactic| simp (config := {decide := true}))

/-- `insert_raw` entry locals. -/
def irP0 (T Kk V : BitVec 64) : List (MlS × BitVec 64) :=
  [(ofString "t",T),(ofString "key",Kk),(ofString "value",V)]

/-- `insert_raw` locals after the header loads. -/
def irP7 (T Kk V KL SD C KS US OS OPS : BitVec 64) : List (MlS × BitVec 64) :=
  [(ofString "order_pos",OPS),(ofString "order",OS),(ofString "used",US),(ofString "keys",KS),
    (ofString "stride",SD),(ofString "klen",KL),(ofString "cap",C),(ofString "t",T),(ofString "key",Kk),
    (ofString "value",V)]

/-- A header load `name = lds (t + off)` into a fresh scalar local. -/
theorem aqm_hdrDec {R : Mem → Prop} {pairs : List (MlS × BitVec 64)} {T : BitVec 64} (name : MlS) (off val : BitVec 64)
    {body : ProgHOL 64} (hname : ∀ p ∈ pairs, p.1 ≠ name) (ht : (ofString "t",T) ∈ pairs)
    (hval : ∀ M, R M → M (T + off) = .word val)
    (hb : AQM SP0 P0 FM G0 w (fun _ => True) (fun L M => LK ((name,val) :: pairs) L ∧ R M) (fun _ _ => True) RR body) :
    AQM SP0 P0 FM G0 w (fun _ => True) (fun L M => LK pairs L ∧ R M) (fun _ _ => True) RR
      (.dec name .one (.load .one (.op .add [.var .local (ofString "t"),.const off])) body) :=
  aqm_dec name .one _ (fun _ => rfl)
    (fun s v _ ⟨hl,hm⟩ _ ev _ => by
      rw [ev_load_off s _ T off v (lk_get hl _ _ ht) ev,hval _ hm]
      exact ⟨lk_cons hl _ _ hname,hm⟩)
    hb (fun _ _ _ _ _ _ => trivial)

set_option maxHeartbeats 4000000 in
/-- `htab_insert_raw` under the real table layout: the watched word outside the table footprint is kept in every
outcome, and a return leaves the header (count incremented) with memory agreeing with the entry outside the
footprint. -/
theorem insertRaw_aqm (T Kk V E KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat)
    (lay : HLay P0 T E KL SD C N KS VS US OS OPS b) (M0 : Mem) (hw : ¬ Foot P0 T E w) :
    AQM SP0 P0 FM G0 w (fun _ => True)
      (fun L M => LK (irP0 T Kk V) L ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0)
      (fun _ _ => True) (fun _ M' => MI P0 T E M0 KL SD C (N + 1#64) KS VS US OS OPS M')
      (sourceFunctionBody Guest.guestFn_htab_insert_raw) := by
  have fitT : T.toNat + 72 < 2 ^ 64 := by have := lay.hdr; have := lay.eEnd; omega
  have cHE : C.toNat ≤ 33806089496 := by have := arr_end lay.usedR lay.eEnd; omega
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_htab_insert_raw,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some]
  refine aqm_conseq (P := fun L M => LK (irP0 T Kk V) L ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) ?_
    (fun L M h => ⟨h.1,h.2.1,fun x _ => by rw [h.2.2]⟩) (fun _ _ h => h) (fun _ _ h => h)
  refine aqm_hdrDec (ofString "cap") 16#64 C (by unfold irP0; lkne) (by simp [irP0]) (fun M h => h.1.2.2.1) ?_
  refine aqm_hdrDec (ofString "klen") 0#64 KL (by unfold irP0; lkne) (by simp [irP0]) (fun M h => h.1.1) ?_
  refine aqm_hdrDec (ofString "stride") 8#64 SD (by unfold irP0; lkne) (by simp [irP0]) (fun M h => h.1.2.1) ?_
  refine aqm_hdrDec (ofString "keys") 32#64 KS (by unfold irP0; lkne) (by simp [irP0]) (fun M h => h.1.2.2.2.2.1) ?_
  refine aqm_hdrDec (ofString "used") 48#64 US (by unfold irP0; lkne) (by simp [irP0])
    (fun M h => h.1.2.2.2.2.2.2.1) ?_
  refine aqm_hdrDec (ofString "order") 56#64 OS (by unfold irP0; lkne) (by simp [irP0])
    (fun M h => h.1.2.2.2.2.2.2.2.1) ?_
  refine aqm_hdrDec (ofString "order_pos") 64#64 OPS (by unfold irP0; lkne) (by simp [irP0])
    (fun M h => h.1.2.2.2.2.2.2.2.2) ?_
  refine aqm_decCallSpec (Vn' := fun _ => False) (Pe := fun _ M0' _ M => M = M0') (RRe := fun _ M0' _ M' => M' = M0')
    (Pc := fun L M => ∃ H : BitVec 64, LK ((ofString "h",H) :: irP7 T Kk V KL SD C KS US OS OPS) L ∧
      MI P0 T E M0 KL SD C N KS VS US OS OPS M)
    (Qc := fun _ _ => True) _ _ _ _ _ _ _ originalRuntimeCode_hash_lookup (by simp) (fun _ M0' _ => hash_aqm M0')
    (fun _ _ _ _ _ _ _ _ _ => rfl) (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ => trivial)
  · intro L M v M' ⟨hl,hm⟩ eM ok
    subst eM
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    exact ⟨y,lk_cons hl _ _ (by unfold irP0; lkne),hm⟩
  refine aqm_dec (Pb := fun L M => ∃ I : BitVec 64, LK ((ofString "i",I) :: irP7 T Kk V KL SD C KS US OS OPS) L ∧
      I.toNat < C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M)
    (Qb := fun _ _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ => trivial)
  · intro F s v _ ⟨H,hl,hm⟩ _ ev _
    have hh := lk_get hl (ofString "h") H (by simp)
    have hc := lk_get hl (ofString "cap") C (by simp [irP7])
    simp [EV,evalHOLExact,evalListHOLExact,hh,hc,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    exact ⟨_,lk_cons (fun p hp => hl p (List.mem_cons_of_mem _ hp)) _ _ (by unfold irP7; lkne),
      mask_lt' H C b lay.pow cHE,hm⟩
  refine aqm_seq (Q := fun L M => ∃ I : BitVec 64, LK ((ofString "i",I) :: irP7 T Kk V KL SD C KS US OS OPS) L ∧
      I.toNat < C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M)
    (aqm_while (C := fun _ _ => True) _ (fun _ _ _ _ _ _ _ => trivial) ?_) ?_
  · refine aqm_assignLocal _ _ ?_
    intro F s v _ ⟨⟨I,hl,_,hm⟩,_⟩ _ ev
    have hi := lk_get hl (ofString "i") I (by simp)
    have hc := lk_get hl (ofString "cap") C (by simp [irP7])
    simp [EV,evalHOLExact,evalListHOLExact,hi,hc,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    exact ⟨_,lk_cons (fun p hp => hl p (List.mem_cons_of_mem _ hp)) _ _ (by unfold irP7; lkne),
      mask_lt' _ C b lay.pow cHE,hm⟩
  refine aqm_seq (Q := fun L M => ∃ I : BitVec 64, LK ((ofString "i",I) :: irP7 T Kk V KL SD C KS US OS OPS) L ∧
      I.toNat < C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) (aqm_callSpec (Vn' := fun _ => False)
    (Pe := fun L0 M0' L M => ∃ I : BitVec 64, L0.lookup (ofString "i") = some (.val (.word I)) ∧
      L.lookup (ofString "dst") = some (.val (.word (KS + I * SD))) ∧ L.lookup (ofString "src") = some (.val (.word Kk)) ∧
      L.lookup (ofString "n") = some (.val (.word KL)) ∧ M = M0')
    (RRe := fun L0 M0' _ M' => ∀ I : BitVec 64, L0.lookup (ofString "i") = some (.val (.word I)) →
      ∀ x, ¬ MWin (KS + I * SD) KL.toNat x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_) ?_
  · intro L0 M0' ⟨I,hl,hI,_⟩
    have hi := lk_get hl (ofString "i") I (by simp)
    have small : KL.toNat + 32 < 2 ^ 64 := by
      have := lay.fits; have := arr_end lay.keysR lay.eEnd
      have : SD.toNat ≤ C.toNat * SD.toNat := Nat.le_mul_of_pos_left _ (by omega)
      omega
    refine aqm_conseq (memcpy_aqm (KS + I * SD) Kk KL small (fun hw' => hw (keys_window lay I hI w hw').1) M0') ?_
      (fun _ _ h => h) ?_
    · intro L M ⟨I',hI',h1,h2,h3,h4⟩
      rw [hi] at hI'; cases hI'
      exact ⟨h1,h2,h3,h4⟩
    · intro v M' h I' hI' x hx
      rw [hi] at hI'; cases hI'
      exact h x hx
  · intro F s values callee rs _ ⟨I,hl,hI,hm⟩ _ args lookup
    have hks := lk_get hl (ofString "keys") KS (by simp [irP7])
    have hi := lk_get hl (ofString "i") I (by simp)
    have hsd := lk_get hl (ofString "stride") SD (by simp [irP7])
    have hk := lk_get hl (ofString "key") Kk (by simp [irP7])
    have hkl := lk_get hl (ofString "klen") KL (by simp [irP7])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hks,hi,hsd,hk,hkl,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_memcpy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨I,hi,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl⟩
  · intro L M v M' ⟨I,hl,hI,hm⟩ h
    exact ⟨I,hl,hI,mi_frame hm fitT _ (keys_window lay I hI) (h I (lk_get hl _ _ (by simp)))⟩
  refine aqm_seq (Q := fun L M => ∃ I : BitVec 64, LK ((ofString "i",I) :: irP7 T Kk V KL SD C KS US OS OPS) L ∧
      I.toNat < C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) (aqm_store' _ _ ?_ ?_) ?_
  · intro F s a _ ⟨I,hl,hI,hm⟩ _ ev
    have ht := lk_get hl (ofString "t") T (by simp [irP7])
    have hi := lk_get hl (ofString "i") I (by simp)
    simp [EV,evalHOLExact,evalListHOLExact,ht,hi,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,memLoadHOLExact,
      hm.1.2.2.2.2.2.1] at ev
    by_cases hd : s.memaddrs (T + 40#64)
    · simp [hd,valueWord] at ev
      subst ev
      obtain ⟨fa,ha⟩ := arr_slot8 lay.valsR lay.eEnd lay.hdrP hI
      exact ⟨fun e => hw (e ▸ fa),fun y _ => ⟨I,hl,hI,mi_write hm fitT _ fa ha (fun x hx => word_update_keep x hx)⟩⟩
    · simp [hd] at ev
  · intro F s x _ ⟨I,hl,_,_⟩ _ ev
    have hv := lk_get hl (ofString "value") V (by simp [irP7])
    simp [EV,evalHOLExact,hv] at ev
    exact ⟨V,ev.symm⟩
  refine aqm_seq (Q := fun L M => ∃ I : BitVec 64, LK ((ofString "i",I) :: irP7 T Kk V KL SD C KS US OS OPS) L ∧
      I.toNat < C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) (aqm_storeByte' _ _ ?_) ?_
  · intro F s a _ ⟨I,hl,hI,hm⟩ _ ev
    have hu := lk_get hl (ofString "used") US (by simp [irP7])
    have hi := lk_get hl (ofString "i") I (by simp)
    simp [EV,evalHOLExact,evalListHOLExact,hu,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    obtain ⟨fa,ha⟩ := arr_byte lay.usedR lay.eEnd lay.hdrP lay.usAl hI
    exact ⟨fun e => hw (e ▸ fa),fun M' hM' => ⟨I,hl,hI,mi_frame hm fitT (· = panByteAlignHOL (US + I))
      (fun x hx => hx ▸ ⟨fa,ha⟩) (fun x hx => hM' x hx)⟩⟩
  refine aqm_dec (Pb := fun L M => ∃ I : BitVec 64, LK ((ofString "n",N) :: (ofString "i",I) :: irP7 T Kk V KL SD C KS US OS OPS) L ∧
      I.toNat < C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) (Qb := fun _ _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ => trivial)
  · intro F s v _ ⟨I,hl,hI,hm⟩ _ ev _
    rw [ev_load_off s _ T 24#64 v (lk_get hl _ _ (by simp [irP7])) ev,hm.1.2.2.2.1]
    exact ⟨I,lk_cons hl _ _ (by unfold irP7; lkne),hI,hm⟩
  refine aqm_seq (Q := fun L M => ∃ I : BitVec 64, LK ((ofString "n",N) :: (ofString "i",I) :: irP7 T Kk V KL SD C KS US OS OPS) L ∧
      I.toNat < C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) (aqm_store' _ _ ?_ ?_) ?_
  · intro F s a _ ⟨I,hl,hI,hm⟩ _ ev
    have ho := lk_get hl (ofString "order") OS (by simp [irP7])
    have hn := lk_get hl (ofString "n") N (by simp)
    simp [EV,evalHOLExact,evalListHOLExact,ho,hn,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord] at ev
    subst ev
    obtain ⟨fa,ha⟩ := arr_slot8 lay.orderR lay.eEnd lay.hdrP lay.cnt
    exact ⟨fun e => hw (e ▸ fa),fun y _ => ⟨I,hl,hI,mi_write hm fitT _ fa ha (fun x hx => word_update_keep x hx)⟩⟩
  · intro F s x _ ⟨I,hl,_,_⟩ _ ev
    have hi := lk_get hl (ofString "i") I (by simp)
    simp [EV,evalHOLExact,hi] at ev
    exact ⟨I,ev.symm⟩
  refine aqm_seq (Q := fun L M => ∃ I : BitVec 64, LK ((ofString "n",N) :: (ofString "i",I) :: irP7 T Kk V KL SD C KS US OS OPS) L ∧
      I.toNat < C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) (aqm_store' _ _ ?_ ?_) ?_
  · intro F s a _ ⟨I,hl,hI,hm⟩ _ ev
    have ho := lk_get hl (ofString "order_pos") OPS (by simp [irP7])
    have hi := lk_get hl (ofString "i") I (by simp)
    simp [EV,evalHOLExact,evalListHOLExact,ho,hi,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord] at ev
    subst ev
    obtain ⟨fa,ha⟩ := arr_slot8 lay.oposR lay.eEnd lay.hdrP hI
    exact ⟨fun e => hw (e ▸ fa),fun y _ => ⟨I,hl,hI,mi_write hm fitT _ fa ha (fun x hx => word_update_keep x hx)⟩⟩
  · intro F s x _ ⟨I,hl,_,_⟩ _ ev
    have hn := lk_get hl (ofString "n") N (by simp)
    simp [EV,evalHOLExact,hn] at ev
    exact ⟨N,ev.symm⟩
  refine aqm_seq (Q := fun L M => ∃ I : BitVec 64, LK ((ofString "n",N) :: (ofString "i",I) :: irP7 T Kk V KL SD C KS US OS OPS) L ∧
      MI P0 T E M0 KL SD C (N + 1#64) KS VS US OS OPS M) (aqm_store' _ _ ?_ ?_) (aqm_return _ ?_)
  · intro F s a _ ⟨I,hl,hI,hm⟩ _ ev
    have ht := lk_get hl (ofString "t") T (by simp [irP7])
    simp [EV,evalHOLExact,evalListHOLExact,ht,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have fa : Foot P0 T E (T + 24#64) := by
      left; rw [BitVec.toNat_add_of_lt (by simp; omega)]; have := lay.hdr; simp; omega
    refine ⟨fun e => hw (e ▸ fa),fun y ey => ?_⟩
    have hn := lk_get hl (ofString "n") N (by simp)
    simp [EV,evalHOLExact,evalListHOLExact,hn,wordOpHOL,wordOp,valueIsWord,valueWord] at ey
    subst ey
    exact ⟨I,hl,mi_count hm lay.hdr (by have := lay.eEnd; omega)⟩
  · intro F s x _ ⟨I,hl,_,_⟩ _ ev
    exact ev_op_word s _ _ x ev
  · intro F s v _ ⟨I,_,hm⟩ _ _
    exact hm

#print axioms aqm_store'
#print axioms aqm_storeByte'
#print axioms mi_count
#print axioms keys_window
#print axioms insertRaw_aqm
end InitECandidate.Runtime
