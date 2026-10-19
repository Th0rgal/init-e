import InitECandidate.Runtime.ArenaFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Scalar locals: every local named in `Vn` that is bound holds a word value. -/
def SL (Vn : MlS → Prop) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∀ x, Vn x → ∀ v, L.lookup x = some v → ∃ y : BitVec 64, v = .val (.word y)

theorem scalar_of_shape {v : ValueHOL 64} (h : shapeEqHOL .one (shapeOfHOLExact v) = true) :
    ∃ y : BitVec 64, v = .val (.word y) := by
  cases v with
  | val x => cases x with | word y => exact ⟨y,rfl⟩
  | rStruct fs => simp [shapeOfHOLExact,shapeEqHOL] at h
  | nStruct n fs => simp [shapeOfHOLExact,shapeEqHOL] at h

theorem scalar_of_shape' {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ y : BitVec 64, v = .val (.word y) := by
  cases v with
  | val x => cases x with | word y => exact ⟨y,rfl⟩
  | rStruct fs => simp [shapeOfHOLExact,shapeEqHOL] at h
  | nStruct n fs => simp [shapeOfHOLExact,shapeEqHOL] at h

theorem sl_update {Vn : MlS → Prop} {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : SL Vn L) (x : MlS)
    (v : ValueHOL 64) (hv : Vn x → ∃ y : BitVec 64, v = .val (.word y)) : SL Vn (L.update (x,v)) := by
  intro z hz u hu
  by_cases e : z = x
  · subst e
    simp [HolFiniteMapExact.lookup_update,FUPDATE] at hu
    subst hu; exact hv hz
  · simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm e] at hu
    exact h z hz u hu

theorem sl_restore {Vn : MlS → Prop} {L L' : HolFiniteMapExact MlS (ValueHOL 64)} (inner : SL Vn L')
    (outer : SL Vn L) (x : MlS) : SL Vn (L'.resVarEq (x,L.lookup x)) := by
  intro z hz u hu
  rw [lookup_resVarEq_toExact] at hu
  cases hx : L.lookup x with
  | none =>
    simp only [resVarHOLExact,hx] at hu
    split at hu
    · cases hu
    · exact inner z hz u hu
  | some old =>
    simp only [resVarHOLExact,hx] at hu
    split at hu
    · rename_i e; subst e; simp only [Option.some.injEq] at hu; subst hu; exact outer z hz old hx
    · exact inner z hz u hu

theorem sl_empty (Vn : MlS → Prop) : SL Vn (HolFiniteMapExact.empty) := by
  intro z _ u hu; simp [HolFiniteMapExact.lookup_empty] at hu

/-- A successful lookup of a function whose parameters are all one-word binds only word values. -/
theorem lookupCode_callee_scalar (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (f : MlS) (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL) (params : List (MlS × ShapeHOL)) (body' : ProgHOL 64) (rs' : ShapeHOL)
    (hcode : code f = some (params,body',rs')) (allOne : ∀ p ∈ params, p.2 = .one)
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite code f values = some (body,callee,rs)) (Vn : MlS → Prop) : SL Vn callee := by
  have key : ∀ (pairs : List (MlS × ValueHOL 64)) (m : MlS → Option (ValueHOL 64)),
      (∀ x v, m x = some v → ∃ y : BitVec 64, v = .val (.word y)) →
      (∀ e ∈ pairs, ∃ y : BitVec 64, e.2 = .val (.word y)) →
      ∀ x v, (pairs.foldl (fun (map : MlS → Option (ValueHOL 64)) (entry : MlS × ValueHOL 64) =>
        fun current => if current = entry.1 then some entry.2 else map current) m) x = some v →
        ∃ y : BitVec 64, v = .val (.word y) := by
    intro pairs
    induction pairs with
    | nil => intro m hm _ x v hx; exact hm x v hx
    | cons e rest ih =>
      intro m hm he x v hx
      refine ih _ ?_ (fun e' m' => he e' (List.mem_cons_of_mem _ m')) x v hx
      intro x' v' hx'
      dsimp only at hx'
      split at hx'
      · simp only [Option.some.injEq] at hx'; subst hx'; exact he e List.mem_cons_self
      · exact hm x' v' hx'
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i b cl r hl
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨_,hcl,_⟩ := h
    subst hcl
    unfold lookupCodeHOLExact at hl
    rw [hcode] at hl
    dsimp only at hl
    split at hl
    · rename_i hcond
      simp only [Option.some.injEq,Prod.mk.injEq] at hl
      obtain ⟨_,hcl',_⟩ := hl
      intro z _ u hu
      change cl z = some u at hu
      subst hcl'
      refine key _ (fun _ => none) (fun _ _ hx => by cases hx) ?_ z u hu
      intro e he
      rw [List.zip_map_left] at he
      obtain ⟨⟨p,v⟩,hm,rfl⟩ := List.mem_map.mp he
      have hall := List.all_eq_true.mp hcond.2.2 (p,v) hm
      have hp := allOne p (List.of_mem_zip hm).1
      simp only at hall
      rw [hp] at hall
      exact scalar_of_shape hall
    · cases hl



/-- Expression evaluation in a finite state (the evaluator's own decider). -/
noncomputable abbrev EV {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) : Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e

/-- Memory domain bound: every addressable word lies below `2^62` (the actual domain is a bounded word range). -/
def DomOK (m : BitVec 64 → Prop) : Prop := ∀ a : BitVec 64, m a → a.toNat < 2^62

/-- Arena triple: from an arena state with scalar locals satisfying `P`, the watched word is kept in every outcome,
the arena globals on continuing outcomes, a normal outcome has scalar locals satisfying `Q`, and no `break` or
`continue` escapes. -/
def AQ (SP0 P0 FM w : BitVec 64) (Vn : MlS → Prop) (P Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (p : ProgHOL 64) : Prop :=
  ∀ (F : Type) (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomOK s.memaddrs →
    AW SP0 P0 FM s.globals → SL Vn s.locals → P s.locals →
    (evaluateHOLFiniteState s p).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s p).1 → AW SP0 P0 FM (evaluateHOLFiniteState s p).2.globals) ∧
    ((evaluateHOLFiniteState s p).1 = none → SL Vn (evaluateHOLFiniteState s p).2.locals ∧
      Q (evaluateHOLFiniteState s p).2.locals) ∧
    (evaluateHOLFiniteState s p).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p).1 ≠ some .break

variable {SP0 P0 FM w : BitVec 64} {Vn : MlS → Prop}

theorem aq_conseq {P P' Q Q' : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {p : ProgHOL 64}
    (h : AQ SP0 P0 FM w Vn P Q p) (hp : ∀ L, P' L → P L) (hq : ∀ L, Q L → Q' L) : AQ SP0 P0 FM w Vn P' Q' p := by
  intro F s code dom aw sl pre
  obtain ⟨m,a,n,c,b⟩ := h F s code dom aw sl (hp _ pre)
  exact ⟨m,a,fun e => ⟨(n e).1,hq _ (n e).2⟩,c,b⟩

theorem aq_seq {P Q R : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {p q : ProgHOL 64}
    (hp : AQ SP0 P0 FM w Vn P Q p) (hq : AQ SP0 P0 FM w Vn Q R q) : AQ SP0 P0 FM w Vn P R (.seq p q) := by
  intro F s code dom aw sl pre
  have h1 := hp F s code dom aw sl pre
  have meta' := evaluateHOLFiniteState_metadata s p
  rw [evaluateHOLFiniteState_seq_line780]
  cases r : evaluateHOLFiniteState s p with
  | mk res m =>
    rw [r] at h1 meta'
    obtain ⟨m1,a1,n1,c1,b1⟩ := h1
    cases res with
    | some x => exact ⟨m1,a1,(fun e => by cases e),c1,b1⟩
    | none =>
      obtain ⟨sl1,q1⟩ := n1 rfl
      obtain ⟨m2,a2,n2,c2,b2⟩ := hq F m (meta'.1.trans code) (by rw [meta'.2.1]; exact dom) (a1 (Or.inl rfl)) sl1 q1
      exact ⟨m2.trans m1,a2,n2,c2,b2⟩

theorem aq_skip {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} : AQ SP0 P0 FM w Vn P P .skip := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_skip]
  exact ⟨rfl,fun _ => aw,fun _ => ⟨sl,pre⟩,by simp,by simp⟩

theorem aq_ite {P Q CT CF : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (c : ExpHOL 64) {y n : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), AW SP0 P0 FM s.globals → P s.locals →
      SL Vn s.locals → EV s c = some (.val (.word x)) → (x ≠ 0 → CT s.locals) ∧ (x = 0 → CF s.locals))
    (hy : AQ SP0 P0 FM w Vn (fun L => P L ∧ CT L) Q y) (hn : AQ SP0 P0 FM w Vn (fun L => P L ∧ CF L) Q n) :
    AQ SP0 P0 FM w Vn P Q (.ite c y n) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i x hx
    have cc := hc s x aw pre sl hx
    split
    · rename_i z; exact hn F s code dom aw sl ⟨pre,cc.2 z⟩
    · rename_i z; exact hy F s code dom aw sl ⟨pre,cc.1 z⟩
  · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩

theorem aq_while_run {I C : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (c : ExpHOL 64) (body : ProgHOL 64)
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), AW SP0 P0 FM s.globals → I s.locals →
      SL Vn s.locals → EV s c = some (.val (.word x)) → x ≠ 0 → C s.locals)
    (hb : AQ SP0 P0 FM w Vn (fun L => I L ∧ C L) I body) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode) (dom : DomOK s.memaddrs)
    (aw : AW SP0 P0 FM s.globals)
    (sl : SL Vn s.locals) (pre : I s.locals) :
    (evaluateHOLFiniteState s (.while c body)).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s (.while c body)).1 →
      AW SP0 P0 FM (evaluateHOLFiniteState s (.while c body)).2.globals) ∧
    ((evaluateHOLFiniteState s (.while c body)).1 = none → SL Vn (evaluateHOLFiniteState s (.while c body)).2.locals ∧
      I (evaluateHOLFiniteState s (.while c body)).2.locals) ∧
    (evaluateHOLFiniteState s (.while c body)).1 ≠ some .continue ∧
    (evaluateHOLFiniteState s (.while c body)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · rename_i x hx
    rw [evalHOLFinite_eq_toExact] at hx
    split
    · rename_i nz
      split
      · exact ⟨rfl,(fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h),(fun e => by cases e),by simp,by simp⟩
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have st := hb F (decClockHOLFinite s) code dom aw sl ⟨pre,hc s x aw pre sl hx nz⟩
        have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        cases run : evaluateHOLFiniteState (decClockHOLFinite s) body with
        | mk result middle =>
          rw [run] at st meta' remaining
          obtain ⟨m1,a1,n1,c1,b1⟩ := st
          have smaller : middle.clock < s.clock := by
            change middle.clock ≤ s.clock - 1 at remaining
            omega
          cases result with
          | none =>
            obtain ⟨sl1,i1⟩ := n1 rfl
            have again := aq_while_run c body hc hb middle (meta'.1.trans code) (by rw [meta'.2.1]; exact dom) (a1 (Or.inl rfl)) sl1 i1
            exact ⟨again.1.trans m1,again.2⟩
          | some result =>
            cases result with
            | «continue» => exact absurd rfl c1
            | «break» => exact absurd rfl b1
            | returned v => exact ⟨m1,a1,(fun e => by cases e),by simp,by simp⟩
            | exception _ _ => exact ⟨m1,a1,(fun e => by cases e),by simp,by simp⟩
            | finalFfi _ => exact ⟨m1,a1,(fun e => by cases e),by simp,by simp⟩
            | error => exact ⟨m1,a1,(fun e => by cases e),by simp,by simp⟩
            | timeOut => exact ⟨m1,a1,(fun e => by cases e),by simp,by simp⟩
    · exact ⟨rfl,fun _ => aw,fun _ => ⟨sl,pre⟩,by simp,by simp⟩
  · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
termination_by s.clock

theorem aq_while {I C : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (c : ExpHOL 64) {body : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), AW SP0 P0 FM s.globals → I s.locals →
      SL Vn s.locals → EV s c = some (.val (.word x)) → x ≠ 0 → C s.locals)
    (hb : AQ SP0 P0 FM w Vn (fun L => I L ∧ C L) I body) : AQ SP0 P0 FM w Vn I I (.while c body) :=
  fun F s code dom aw sl pre => aq_while_run c body hc hb s code dom aw sl pre

theorem aq_dec {P Pb Qb Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (name : MlS) (shape : ShapeHOL)
    (init : ExpHOL 64) {body : ProgHOL 64} (hshape : Vn name → shape = .one)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, AW SP0 P0 FM s.globals → P s.locals → SL Vn s.locals →
      EV s init = some v → shapeEqHOL shape (shapeOfHOLExact v) = true → Pb (s.locals.update (name,v)))
    (hb : AQ SP0 P0 FM w Vn Pb Qb body)
    (hq : ∀ L L', P L → Qb L' → Q (L'.resVarEq (name,L.lookup name))) :
    AQ SP0 P0 FM w Vn P Q (.dec name shape init body) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
  · rename_i v hv
    split
    · rename_i hs
      have slb : SL Vn (setVarHOLFinite name v s).locals :=
        sl_update sl name v (fun hn => by rw [hshape hn] at hs; exact scalar_of_shape hs)
      obtain ⟨m1,a1,n1,c1,b1⟩ := hb F (setVarHOLFinite name v s) (by exact code) (by exact dom) (by exact aw) slb (hi s v aw pre sl hv hs)
      exact ⟨m1,a1,fun e => ⟨sl_restore (n1 e).1 sl name,hq _ _ pre (n1 e).2⟩,c1,b1⟩
    · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩

theorem aq_assignLocal {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (x : MlS) (e : ExpHOL 64)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, AW SP0 P0 FM s.globals → P s.locals → SL Vn s.locals →
      EV s e = some v → Q (s.locals.update (x,v))) :
    AQ SP0 P0 FM w Vn P Q (.assign .local x e) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_assign]
  split
  · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
  · rename_i v hv
    split
    · rename_i valid
      refine ⟨rfl,fun _ => aw,fun _ => ⟨?_,hi s v aw pre sl hv⟩,by simp,by simp⟩
      apply sl_update sl x v
      intro hx
      simp only [isValidValueHOLFinite,lookupKvarHOLFinite] at valid
      split at valid
      · rename_i old hold
        obtain ⟨y,rfl⟩ := sl x hx old hold
        exact scalar_of_shape' (by simpa [shapeOfHOLExact] using valid)
      · cases valid
    · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩

theorem aq_store {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), AW SP0 P0 FM s.globals → P s.locals → SL Vn s.locals →
      ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ w ≠ a)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, P s.locals → SL Vn s.locals → EV s v = some x →
      ∃ y : BitVec 64, x = .val (.word y)) :
    AQ SP0 P0 FM w Vn P P (.store d v) := by
  intro F s code dom aw sl pre
  obtain ⟨a,ha,ne⟩ := hd s aw pre sl
  obtain ⟨res,_,loc,glob,mem⟩ := evaluate_store_word_frame s d v a ha (hv s · pre sl)
  refine ⟨mem w ne,fun _ => by rw [glob]; exact aw,fun _ => by rw [loc]; exact ⟨sl,pre⟩,?_,?_⟩ <;>
    rcases res with h | h <;> rw [h] <;> simp

theorem aq_return {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (e : ExpHOL 64) :
    AQ SP0 P0 FM w Vn P Q (.return e) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_return]
  split
  · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
  · split
    · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
    · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩

theorem aq_raise {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (eid : MlS) (e : ExpHOL 64) :
    AQ SP0 P0 FM w Vn P Q (.raise eid e) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · exact ⟨rfl,(fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h),(fun e => by cases e),by simp,by simp⟩
    · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
  · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩

theorem sl_var {L : HolFiniteMapExact MlS (ValueHOL 64)} {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : s.locals = L) (h : SL Vn L) (x : MlS) (hx : Vn x) (v : ValueHOL 64)
    (ev : EV s (.var .local x) = some v) : ∃ y : BitVec 64, v = .val (.word y) := by
  subst hs
  simp [EV,evalHOLExact] at ev
  exact h x hx v ev


theorem sl_mono {Vn' : MlS → Prop} {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : SL Vn L) (hv : ∀ x, Vn' x → Vn x) :
    SL Vn' L := fun x hx v hl => h x (hv x hx) v hl

/-- Callee obligation: from an arena entry state whose locals are all one-word, the watched word is kept in every
outcome and the arena globals on continuing outcomes. -/
def ACallee (SP0 P0 FM w : BitVec 64) (body : ProgHOL 64) : Prop :=
  ∀ (F : Type) (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomOK s.memaddrs →
    AW SP0 P0 FM s.globals → SL (fun _ => True) s.locals →
    (evaluateHOLFiniteState s body).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s body).1 → AW SP0 P0 FM (evaluateHOLFiniteState s body).2.globals)

theorem acallee_of_asafe {body : ProgHOL 64} (h : ASafe SP0 P0 FM w body) : ACallee SP0 P0 FM w body :=
  fun _ s code _ aw _ => h s code aw

theorem acallee_of_aq {Vn' : MlS → Prop} {Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {body : ProgHOL 64}
    (h : AQ SP0 P0 FM w Vn' (fun _ => True) Q body) : ACallee SP0 P0 FM w body := by
  intro F s code dom aw sl
  obtain ⟨m,a,_⟩ := h F s code dom aw (sl_mono sl (fun _ _ => trivial)) trivial
  exact ⟨m,a⟩

theorem callee_entry_sl (function : MlS) (values : List (ValueHOL 64)) (parameters : List (MlS × ShapeHOL))
    (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (found : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (foundShape : ShapeHOL)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape)) :
    SL (fun _ => True) callee :=
  lookupCode_callee_scalar _ function values found callee foundShape parameters body returnShape installed allOne
    lookup _

theorem aq_of_not_continuing {Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)} (m : t.memory w = s.memory w)
    (h : ¬ Continuing r) :
    (r,t).2.memory w = s.memory w ∧ (Continuing (r,t).1 → AW SP0 P0 FM (r,t).2.globals) ∧
      ((r,t).1 = none → SL Vn (r,t).2.locals ∧ Q (r,t).2.locals) ∧ (r,t).1 ≠ some .continue ∧
      (r,t).1 ≠ some .break :=
  ⟨m,fun c => absurd c h,fun e => absurd (Or.inl e) h,fun e => h (Or.inr (Or.inl e)),
    fun e => h (Or.inr (Or.inr (Or.inl e)))⟩

theorem aq_call {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (hb : ACallee SP0 P0 FM w body) :
    AQ SP0 P0 FM w Vn P P (.call (some (none,none)) function arguments) := by
  intro F state code dom aw sl pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have esl := callee_entry_sl function values parameters found returnShape installed allOne found callee foundShape
        (by rw [← code]; exact lookup)
      split
      · exact aq_of_not_continuing rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb F (callEntryStateHOLFinite state callee) code dom aw esl
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          change bodyPost.memory w = state.memory w ∧ (Continuing rb → AW SP0 P0 FM bodyPost.globals) at frame
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals first
            | exact ⟨frame.1,fun _ => frame.2 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),fun _ => ⟨sl,pre⟩,by simp,by simp⟩
            | exact aq_of_not_continuing frame.1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aq_tailCall {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (function : MlS)
    (arguments : List (ExpHOL 64)) (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (hb : ACallee SP0 P0 FM w body) :
    AQ SP0 P0 FM w Vn P Q (.call none function arguments) := by
  intro F state code dom aw sl pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have esl := callee_entry_sl function values parameters found returnShape installed allOne found callee foundShape
        (by rw [← code]; exact lookup)
      split
      · exact aq_of_not_continuing rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb F (callEntryStateHOLFinite state callee) code dom aw esl
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          change bodyPost.memory w = state.memory w ∧ (Continuing rb → AW SP0 P0 FM bodyPost.globals) at frame
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals first
            | exact ⟨frame.1,fun _ => frame.2 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),(fun e => by cases e),by simp,by simp⟩
            | exact aq_of_not_continuing frame.1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- A discarded call with an exception handler: the handler, entered from any state with the original code, keeps
the watched word and never continues (it re-raises). -/
theorem aq_callHandler {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (function : MlS)
    (arguments : List (ExpHOL 64)) (eid ev : MlS) (handler : ProgHOL 64)
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (hb : ACallee SP0 P0 FM w body)
    (hh : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      (evaluateHOLFiniteState s handler).2.memory w = s.memory w ∧ ¬ Continuing (evaluateHOLFiniteState s handler).1) :
    AQ SP0 P0 FM w Vn P P (.call (some (none,some (eid,ev,handler))) function arguments) := by
  intro F state code dom aw sl pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have esl := callee_entry_sl function values parameters found returnShape installed allOne found callee foundShape
        (by rw [← code]; exact lookup)
      split
      · exact aq_of_not_continuing rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb F (callEntryStateHOLFinite state callee) code dom aw esl
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame meta'
          change bodyPost.memory w = state.memory w ∧ (Continuing rb → AW SP0 P0 FM bodyPost.globals) at frame
          obtain ⟨H,hH⟩ : ∃ H : PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F,
              H = fun t => evaluateHOLFiniteState t handler := ⟨_,rfl⟩
          have hh' : ∀ t : PanSemStateFiniteExact 64 F, t.code = originalRuntimeCode →
              (H t).2.memory w = t.memory w ∧ ¬ Continuing (H t).1 := by subst hH; exact fun t c => hh t c
          have eqH : ∀ t : PanSemStateFiniteExact 64 F, evaluateHOLFiniteState t handler = H t := by
            subst hH; intro; rfl
          simp only [eqH]
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (repeat' split)
          all_goals first
            | exact ⟨frame.1,fun _ => frame.2 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),fun _ => ⟨sl,pre⟩,by simp,by simp⟩
            | exact aq_of_not_continuing frame.1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
            | (refine aq_of_not_continuing ((hh' _ ?_).1.trans frame.1) (hh' _ ?_).2 <;>
                exact meta'.1.trans code)

theorem lookupCodeHOLFinite_installed_shape
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name : MlS) (parameters : List (MlS × ShapeHOL)) (body foundBody : ProgHOL 64)
    (returnShape foundShape : ShapeHOL) (values : List (ValueHOL 64))
    (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (installed : code name = some (parameters,body,returnShape))
    (found : lookupCodeHOLFinite code name values = some (foundBody,locals,foundShape)) :
    foundShape = returnShape := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i exactBody exactLocals exactShape raw
    have same : exactShape = returnShape := by
      simp only [lookupCodeHOLExact,installed] at raw
      split at raw
      · exact ((Prod.mk.inj (Prod.mk.inj (Option.some.inj raw)).2).2).symm
      · cases raw
    have equal := Option.some.inj found
    exact ((Prod.mk.inj (Prod.mk.inj equal).2).2).symm.trans same

theorem aq_decCall {P Pc Qc Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (hb : ACallee SP0 P0 FM w body) (hshape : Vn name → shape = .one)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee post v, s.code = originalRuntimeCode →
      AW SP0 P0 FM s.globals → SL Vn s.locals → P s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,returnShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v),post) →
      shapeEqHOL (shapeOfHOLExact v) shape = true → Pc (s.locals.update (name,v)))
    (hc : AQ SP0 P0 FM w Vn Pc Qc cont)
    (hq : ∀ L L', P L → Qc L' → Q (L'.resVarEq (name,L.lookup name))) :
    AQ SP0 P0 FM w Vn P Q (.decCall name shape function arguments cont) := by
  intro F state code dom aw sl pre
  rw [evaluateHOLFiniteState_decCall_total]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have same2 : foundShape = returnShape :=
        lookupCodeHOLFinite_installed_shape state.code.lookup function parameters found found returnShape
          foundShape values callee (by rw [code]; exact installed) lookup
      subst same2
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      have esl := callee_entry_sl function values parameters found foundShape installed allOne found callee foundShape
        lookup'
      split
      · exact aq_of_not_continuing rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb F (callEntryStateHOLFinite state callee) code dom aw esl
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame meta'
          change bodyPost.memory w = state.memory w ∧ (Continuing rb → AW SP0 P0 FM bodyPost.globals) at frame
          dsimp only [fixClockHOLFinite]
          cases rb with
          | none => exact aq_of_not_continuing frame.1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · rename_i ok
                simp only [Bool.and_eq_true] at ok
                have cslx : SL Vn (state.locals.update (name,v)) :=
                  sl_update sl name v (fun hn => by rw [hshape hn] at ok; exact scalar_of_shape' ok.1)
                have pc := hret state values callee bodyPost v code aw sl pre args lookup' bodyRun ok.1
                obtain ⟨m2,a2,n2,c2,b2⟩ := hc F (setVarHOLFinite name v { bodyPost with clock := _, locals := state.locals })
                  (by exact meta'.1.trans code) (by intro a ha; exact dom a (meta'.2.1 ▸ ha)) (by exact frame.2 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))) cslx pc
                exact ⟨m2.trans frame.1,a2,fun e => ⟨sl_restore (n2 e).1 sl name,hq _ _ pre (n2 e).2⟩,c2,b2⟩
              · exact aq_of_not_continuing frame.1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
            | _ => exact aq_of_not_continuing frame.1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)


/-- A `trap_with(k)` call keeps all memory and never continues. -/
theorem aq_trapCall {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (k : BitVec 64) :
    AQ SP0 P0 FM w Vn P Q (.call (some (none,none)) (ofString "trap_with") [.const k]) := by
  intro F s code dom aw sl pre
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const k] =
      some [.val (.word k)] := by rw [evalListHOLFinite_eq_toExact]; rfl
  have term := evaluate_trap_call_terminal s (.const k) k code args
  have nr := discard_call_not_returned s (ofString "trap_with") [.const k]
  have lc := discard_call_not_loopControl s (ofString "trap_with") [.const k]
  have mk := memKeep_discardCall (ofString "trap_with") [.const k] _ _ _ originalRuntimeCode_trap_lookup trapWith_memKeep s code
  cases hr : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "trap_with") [.const k]) with
  | mk r t =>
    rw [hr] at term lc mk
    have nr' : ∀ v, r ≠ some (.returned v) := fun v => by have := nr v; rw [hr] at this; exact this
    refine aq_of_not_continuing (congrFun mk w) ?_
    rintro (h | h | h | ⟨v,h⟩)
    · exact term h
    · exact lc.1 h
    · exact lc.2 h
    · exact nr' v h

/-- Assigning `scratch_ptr` a word in `[FM, SP0]` keeps the arena globals. -/
theorem aq_assignScratch {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (e : ExpHOL 64)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, AW SP0 P0 FM s.globals → P s.locals → SL Vn s.locals →
      EV s e = some v → ∃ q : BitVec 64, v = .val (.word q) ∧ FM.toNat ≤ q.toNat ∧ q.toNat ≤ SP0.toNat) :
    AQ SP0 P0 FM w Vn P P (.assign .global (ofString "scratch_ptr") e) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_assign]
  split
  · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
  · rename_i v hv
    split
    · obtain ⟨q,rfl,lo,hi'⟩ := hi s v aw pre sl hv
      obtain ⟨hf,_,⟨h,hh,hle,hend⟩⟩ := aw
      refine ⟨rfl,fun _ => ⟨?_,⟨q,?_,lo,hi'⟩,⟨h,?_,hle,hend⟩⟩,fun _ => ⟨sl,pre⟩,by simp,by simp⟩
      all_goals simp (config := {decide := true}) [setKvarHOLFinite,setGlobalHOLFinite,
        HolFiniteMapExact.lookup_update,FUPDATE,hf,hh]
    · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩


/-- The all-`True` arena triple. -/
def AQT (SP0 P0 FM w : BitVec 64) (Vn : MlS → Prop) (p : ProgHOL 64) : Prop :=
  AQ SP0 P0 FM w Vn (fun _ => True) (fun _ => True) p


theorem aqT_seq {p q : ProgHOL 64} (hp : AQT SP0 P0 FM w Vn p) (hq : AQT SP0 P0 FM w Vn q) :
    AQT SP0 P0 FM w Vn (.seq p q) := by
  unfold AQT at *; exact aq_seq hp hq

theorem aqT_ite (c : ExpHOL 64) {y n : ProgHOL 64} (hy : AQT SP0 P0 FM w Vn y) (hn : AQT SP0 P0 FM w Vn n) :
    AQT SP0 P0 FM w Vn (.ite c y n) := by
  unfold AQT at *
  exact aq_ite (CT := fun _ => True) (CF := fun _ => True) c (fun _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
    (aq_conseq hy (fun _ _ => trivial) (fun _ h => h)) (aq_conseq hn (fun _ _ => trivial) (fun _ h => h))

theorem aqT_while (c : ExpHOL 64) {body : ProgHOL 64} (hb : AQT SP0 P0 FM w Vn body) :
    AQT SP0 P0 FM w Vn (.while c body) := by
  unfold AQT at *
  exact aq_while (C := fun _ => True) c (fun _ _ _ _ _ _ _ => trivial) (aq_conseq hb (fun _ _ => trivial) (fun _ h => h))

theorem aqT_dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} (hshape : Vn name → shape = .one)
    (hb : AQT SP0 P0 FM w Vn body) : AQT SP0 P0 FM w Vn (.dec name shape init body) := by
  unfold AQT at *
  exact aq_dec name shape init hshape (fun _ _ _ _ _ _ _ => trivial) hb (fun _ _ _ _ => trivial)

theorem aqT_assignLocal (x : MlS) (e : ExpHOL 64) : AQT SP0 P0 FM w Vn (.assign .local x e) := by
  unfold AQT
  exact aq_assignLocal x e (fun _ _ _ _ _ _ => trivial)

theorem aqT_decCall (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (hb : ACallee SP0 P0 FM w body) (hshape : Vn name → shape = .one)
    (hc : AQT SP0 P0 FM w Vn cont) : AQT SP0 P0 FM w Vn (.decCall name shape function arguments cont) := by
  unfold AQT at *
  exact aq_decCall name function shape arguments parameters body returnShape installed allOne hb hshape
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) hc (fun _ _ _ _ => trivial)

theorem aqT_return (e : ExpHOL 64) : AQT SP0 P0 FM w Vn (.return e) := by
  unfold AQT; exact aq_return e



/-- Assigning `heap_ptr` a word in `[P0, HEAP_END]` keeps the arena globals. -/
theorem aq_assignHeap {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (e : ExpHOL 64)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, AW SP0 P0 FM s.globals → P s.locals → SL Vn s.locals →
      EV s e = some v → ∃ q : BitVec 64, v = .val (.word q) ∧ P0.toNat ≤ q.toNat ∧ q.toNat ≤ 33806089496) :
    AQ SP0 P0 FM w Vn P P (.assign .global (ofString "heap_ptr") e) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_assign]
  split
  · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
  · rename_i v hv
    split
    · obtain ⟨q,rfl,lo,hi'⟩ := hi s v aw pre sl hv
      obtain ⟨hf,⟨sp,hsp,a1,a2⟩,_⟩ := aw
      refine ⟨rfl,fun _ => ⟨?_,⟨sp,?_,a1,a2⟩,⟨q,?_,lo,hi'⟩⟩,fun _ => ⟨sl,pre⟩,by simp,by simp⟩
      all_goals simp (config := {decide := true}) [setKvarHOLFinite,setGlobalHOLFinite,
        HolFiniteMapExact.lookup_update,FUPDATE,hf,hsp]
    · exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩

theorem scratchEnd_bound (sp FM n : BitVec 64) (hfm : FM.toNat ≤ sp.toNat) (hn : n ≤ sp - FM) :
    (scratchAllocationEnd sp n).toNat + n.toNat ≤ sp.toNat := by
  have h1 : (sp - FM).toNat = sp.toNat - FM.toNat := by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hfm)]
  have h2 : n.toNat ≤ (sp - FM).toNat := BitVec.le_def.mp hn
  have h3 : (sp - n).toNat = sp.toNat - n.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
  have h4 : (scratchAllocationEnd sp n).toNat ≤ (sp - n).toNat := by
    unfold scratchAllocationEnd; rw [BitVec.toNat_and]; exact Nat.and_le_left
  omega

/-- `scratch_alloc` entry: `p` holds the scratch pointer, in `[FM, SP0]`. -/
def SAp (SP0 FM : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ sp : BitVec 64, L.lookup (ofString "p") = some (.val (.word sp)) ∧ FM.toNat ≤ sp.toNat ∧ sp.toNat ≤ SP0.toNat

/-- After the request guard: the request `n` fits above the frame pointer. -/
def SAn (SP0 FM : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ sp n : BitVec 64, L.lookup (ofString "p") = some (.val (.word sp)) ∧ FM.toNat ≤ sp.toNat ∧
    sp.toNat ≤ SP0.toNat ∧ L.lookup (ofString "n") = some (.val (.word n)) ∧ n ≤ sp - FM

def SAq (SP0 : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ q : BitVec 64, L.lookup (ofString "q") = some (.val (.word q)) ∧ q.toNat ≤ SP0.toNat

def SAq2 (SP0 FM : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ q : BitVec 64, L.lookup (ofString "q") = some (.val (.word q)) ∧ FM.toNat ≤ q.toNat ∧ q.toNat ≤ SP0.toNat

/-- `scratch_alloc` keeps every word of memory in every outcome, and every continuing outcome leaves the scratch
pointer in `[FM, SP0]` with the frame and heap pointers untouched. -/
theorem scratchAlloc_aq :
    AQ SP0 P0 FM w (fun _ => True) (fun _ => True) (fun _ => True) (sourceFunctionBody Guest.guestFn_scratch_alloc) := by
  rw [source_scratch_alloc_body]
  unfold scratchAllocationAfterPointer scratchAllocationFinish
  refine aq_dec (Pb := SAp SP0 FM) (Qb := fun _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s v aw _ _ ev _
    obtain ⟨_,⟨sp,hsp,lo,hi⟩,_⟩ := aw
    simp [EV,evalHOLExact,hsp] at ev
    subst ev
    exact ⟨sp,by simp [HolFiniteMapExact.lookup_update,FUPDATE],lo,hi⟩
  refine aq_seq (Q := SAn SP0 FM) (aq_ite (CT := fun _ => True) (CF := SAn SP0 FM) _ ?_ (aq_trapCall 7)
    (aq_conseq aq_skip (fun _ h => h) (fun _ h => h.2))) ?_
  · intro F s x aw ⟨sp,hp,lo,hi⟩ sl ev
    refine ⟨fun _ => trivial,fun hx => ?_⟩
    subst hx
    obtain ⟨hf,_,_⟩ := aw
    cases hn : s.locals.lookup (ofString "n") with
    | none =>
      simp [EV,scratchAllocationRequestCheck,evalHOLExact,evalListHOLExact,hp,hf,hn,wordOpHOL,wordOp,valueIsWord,
        valueWord] at ev
    | some nv =>
      obtain ⟨n,rfl⟩ := sl _ trivial nv hn
      refine ⟨sp,n,hp,lo,hi,hn,?_⟩
      simp [EV,scratchAllocationRequestCheck,evalHOLExact,evalListHOLExact,hp,hf,hn,wordOpHOL,wordOp,valueIsWord,
        valueWord,Compiler.Encoders.Asm.wordCmpHOL] at ev
      exact BitVec.le_def.mpr (by omega)
  refine aq_dec (Pb := SAq SP0) (Qb := fun _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s v aw ⟨sp,n,hp,lo,hi,hn,req⟩ _ ev _
    simp only [EV] at ev
    rw [eval_scratchAllocationEndExpression s sp n hp hn] at ev
    cases ev
    have := scratchEnd_bound sp FM n lo req
    exact ⟨scratchAllocationEnd sp n,by simp [HolFiniteMapExact.lookup_update,FUPDATE],by omega⟩
  refine aq_seq (Q := SAq2 SP0 FM) (aq_ite (CT := fun _ => True) (CF := SAq2 SP0 FM) _ ?_ (aq_trapCall 7)
    (aq_conseq aq_skip (fun _ h => h) (fun _ h => h.2))) (aq_seq (aq_assignScratch _ ?_) (aq_return _))
  · intro F s x aw ⟨q,hq,hi⟩ _ ev
    refine ⟨fun _ => trivial,fun hx => ?_⟩
    subst hx
    obtain ⟨hf,_,_⟩ := aw
    simp [EV,evalHOLExact,hq,hf,Compiler.Encoders.Asm.wordCmpHOL] at ev
    exact ⟨q,hq,by omega,hi⟩
  · intro F s v _ ⟨q,hq,lo,hi⟩ _ ev
    simp [EV,evalHOLExact,hq] at ev
    subst ev
    exact ⟨q,rfl,lo,hi⟩

theorem scratchAlloc_acallee : ACallee SP0 P0 FM w (sourceFunctionBody Guest.guestFn_scratch_alloc) :=
  acallee_of_aq scratchAlloc_aq


#print axioms lookupCode_callee_scalar
#print axioms aq_seq
#print axioms aq_while
#print axioms aq_dec
#print axioms aq_assignLocal
#print axioms aq_store
#print axioms aq_call
#print axioms aq_tailCall
#print axioms aq_callHandler
#print axioms aq_decCall
#print axioms aq_trapCall
#print axioms aq_assignScratch
#print axioms scratchAlloc_acallee
end InitECandidate.Runtime
