import InitECandidate.Runtime.ArenaHeapGD
/-!
Loop and domain-aware rules for the fixed-domain triple `AQGD`: local assignment, byte store, the break-aware
loop-body triple `AQGB` (seq/ite/break, lifting from `AQGD`), `while` with breaking bodies, and `ite`/`dec`/`return`/
`store` variants whose side conditions also see `DomD D B s` (memory domain and endianness).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {D : BitVec 64 → Prop} {B : Bool} {A : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {w : BitVec 64}
  {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}

abbrev GA := HolFiniteMapExact MlS (ValueHOL 64)

theorem aqgd_assignLocal {P Q : GA → Mem → GA → Prop} (x : MlS) (e : ExpHOL 64)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, A s.globals → DomD D B s → P s.locals s.memory s.globals →
      SL Vn s.locals → EV s e = some v → Q (s.locals.update (x,v)) s.memory s.globals) :
    AQGD D B A w Vn P Q RR (.assign .local x e) := by
  intro F s code dom aw sl G hG pre
  unfold GIs at hG; subst hG
  rw [evaluateHOLFiniteState_assign]
  split
  · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · rename_i v hv
    split
    · rename_i valid
      refine ⟨rfl,fun _ => aw,fun _ => ⟨?_,_,rfl,hi s v aw dom pre sl hv⟩,(fun v e => by cases e),by simp,by simp⟩
      apply sl_update sl x v
      intro hx
      simp only [isValidValueHOLFinite,lookupKvarHOLFinite] at valid
      split at valid
      · rename_i old hold
        obtain ⟨y,rfl⟩ := sl x hx old hold
        exact scalar_of_shape' (by simpa [shapeOfHOLExact] using valid)
      · cases valid
    · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aqgd_storeByte {P Q : GA → Mem → GA → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals → DomD D B s → P s.locals s.memory s.globals →
      SL Vn s.locals → ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ w ≠ panByteAlignHOL a ∧
        ∀ M' : Mem, (∀ x, x ≠ panByteAlignHOL a → M' x = s.memory x) → Q s.locals M' s.globals) :
    AQGD D B A w Vn P Q RR (.storeByte d v) := by
  intro F s code dom aw sl G hG pre
  unfold GIs at hG; subst hG
  obtain ⟨a,ha,ne,hq⟩ := hd s aw dom pre sl
  obtain ⟨res,_,loc,glob,_,_,_⟩ := evaluate_storeByte_control_frame s d v
  refine ⟨evaluate_storeByte_memory_frame s d v a w ha ne,fun _ => by rw [glob]; exact aw,
    fun _ => ⟨by rw [loc]; exact sl,_,by rw [glob]; rfl,by rw [loc]; exact hq _ (fun x hx =>
      evaluate_storeByte_memory_frame s d v a x ha hx)⟩,?_,?_,?_⟩
  · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
  all_goals rcases res with h | h <;> rw [h] <;> simp

/-- Loop-body triple: like `AQGD` but a top-level `break` is allowed and establishes `Qb`. -/
def AQGB (D : BitVec 64 → Prop) (B : Bool) (A : GA → Prop) (w : BitVec 64) (Vn : MlS → Prop)
    (P Q Qb : GA → Mem → GA → Prop) (RR : ValueHOL 64 → Mem → GA → Prop) (p : ProgHOL 64) : Prop :=
  ∀ (F : Type) (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomD D B s →
    A s.globals → SL Vn s.locals → P s.locals s.memory s.globals →
    (evaluateHOLFiniteState s p).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s p).1 → A (evaluateHOLFiniteState s p).2.globals) ∧
    ((evaluateHOLFiniteState s p).1 = none → SL Vn (evaluateHOLFiniteState s p).2.locals ∧
      Q (evaluateHOLFiniteState s p).2.locals (evaluateHOLFiniteState s p).2.memory
        (evaluateHOLFiniteState s p).2.globals) ∧
    ((evaluateHOLFiniteState s p).1 = some .break → SL Vn (evaluateHOLFiniteState s p).2.locals ∧
      Qb (evaluateHOLFiniteState s p).2.locals (evaluateHOLFiniteState s p).2.memory
        (evaluateHOLFiniteState s p).2.globals) ∧
    (∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) →
      RR v (evaluateHOLFiniteState s p).2.memory (evaluateHOLFiniteState s p).2.globals) ∧
    (evaluateHOLFiniteState s p).1 ≠ some .continue

theorem aqgb_of_nc {Q Qb : GA → Mem → GA → Prop} {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)} (m : t.memory w = s.memory w)
    (h : ¬ Continuing r) (hb : r ≠ some .break) :
    (r,t).2.memory w = s.memory w ∧ (Continuing (r,t).1 → A (r,t).2.globals) ∧
      ((r,t).1 = none → SL Vn (r,t).2.locals ∧ Q (r,t).2.locals (r,t).2.memory (r,t).2.globals) ∧
      ((r,t).1 = some .break → SL Vn (r,t).2.locals ∧ Qb (r,t).2.locals (r,t).2.memory (r,t).2.globals) ∧
      (∀ v, (r,t).1 = some (.returned v) → RR v (r,t).2.memory (r,t).2.globals) ∧
      (r,t).1 ≠ some .continue :=
  ⟨m,fun c => absurd c h,fun e => absurd (Or.inl e) h,fun e => absurd e hb,
    fun v e => absurd (Or.inr (Or.inr (Or.inr ⟨v,e⟩))) h,fun e => h (Or.inr (Or.inl e))⟩

theorem aqgb_of_aqgd {P Q Qb : GA → Mem → GA → Prop} {p : ProgHOL 64} (h : AQGD D B A w Vn P Q RR p) :
    AQGB D B A w Vn P Q Qb RR p := by
  intro F s code dom aw sl pre
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl _ rfl pre
  refine ⟨m,a,fun e => ?_,fun e => absurd e b,fun v e => ?_,c⟩
  · obtain ⟨sl',G',hG',q⟩ := n e
    unfold GIs at hG'; subst hG'; exact ⟨sl',q⟩
  · obtain ⟨G',hG',q⟩ := r v e
    unfold GIs at hG'; subst hG'; exact q

theorem aqgb_seq {P Q R Qb : GA → Mem → GA → Prop} {p q : ProgHOL 64}
    (hp : AQGB D B A w Vn P Q Qb RR p) (hq : AQGB D B A w Vn Q R Qb RR q) :
    AQGB D B A w Vn P R Qb RR (.seq p q) := by
  intro F s code dom aw sl pre
  have h1 := hp F s code dom aw sl pre
  have meta' := evaluateHOLFiniteState_metadata s p
  rw [evaluateHOLFiniteState_seq_line780]
  cases r : evaluateHOLFiniteState s p with
  | mk res m =>
    rw [r] at h1 meta'
    obtain ⟨m1,a1,n1,b1,r1,c1⟩ := h1
    cases res with
    | some x => exact ⟨m1,a1,(fun e => by cases e),b1,r1,c1⟩
    | none =>
      obtain ⟨sl1,q1⟩ := n1 rfl
      obtain ⟨d1,d2,d3⟩ := dom
      obtain ⟨m2,a2,n2,b2,r2,c2⟩ := hq F m (meta'.1.trans code)
        ⟨by rw [meta'.2.1]; exact d1,meta'.2.1.trans d2,meta'.2.2.1.trans d3⟩ (a1 (Or.inl rfl)) sl1 q1
      exact ⟨m2.trans m1,a2,n2,b2,r2,c2⟩

theorem aqgb_ite {P Q Qb CT CF : GA → Mem → GA → Prop} (c : ExpHOL 64) {y n : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), A s.globals → DomD D B s →
      P s.locals s.memory s.globals → SL Vn s.locals → EV s c = some (.val (.word x)) →
      (x ≠ 0 → CT s.locals s.memory s.globals) ∧ (x = 0 → CF s.locals s.memory s.globals))
    (hy : AQGB D B A w Vn (fun L M G => P L M G ∧ CT L M G) Q Qb RR y)
    (hn : AQGB D B A w Vn (fun L M G => P L M G ∧ CF L M G) Q Qb RR n) :
    AQGB D B A w Vn P Q Qb RR (.ite c y n) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i x hx
    have cc := hc s x aw dom pre sl hx
    split
    · rename_i z; exact hn F s code dom aw sl ⟨pre,cc.2 z⟩
    · rename_i z; exact hy F s code dom aw sl ⟨pre,cc.1 z⟩
  · exact aqgb_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h) (by simp)

theorem aqgb_break {P Qb Q : GA → Mem → GA → Prop} (h : ∀ L M G, P L M G → Qb L M G) :
    AQGB D B A w Vn P Q Qb RR .break := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_break]
  exact ⟨rfl,fun _ => aw,(fun e => by cases e),fun _ => ⟨sl,h _ _ _ pre⟩,(fun v e => by cases e),by simp⟩

/-- `while c body` whose body may break: the invariant `I` is kept by normal body runs, a break or a false
condition exits with `Qb` resp. `I`. -/
theorem aqgd_whileBreak_run {I C Qb : GA → Mem → GA → Prop} (c : ExpHOL 64) (body : ProgHOL 64)
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), A s.globals → DomD D B s →
      I s.locals s.memory s.globals → SL Vn s.locals → EV s c = some (.val (.word x)) → x ≠ 0 →
      C s.locals s.memory s.globals)
    (hb : AQGB D B A w Vn (fun L M G => I L M G ∧ C L M G) I Qb RR body) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode) (dom : DomD D B s)
    (aw : A s.globals) (sl : SL Vn s.locals) (pre : I s.locals s.memory s.globals) :
    (evaluateHOLFiniteState s (.while c body)).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s (.while c body)).1 →
      A (evaluateHOLFiniteState s (.while c body)).2.globals) ∧
    ((evaluateHOLFiniteState s (.while c body)).1 = none → SL Vn (evaluateHOLFiniteState s (.while c body)).2.locals ∧
      ∃ G', GIs (evaluateHOLFiniteState s (.while c body)).2.globals G' ∧
        (I (evaluateHOLFiniteState s (.while c body)).2.locals (evaluateHOLFiniteState s (.while c body)).2.memory G' ∨
         Qb (evaluateHOLFiniteState s (.while c body)).2.locals (evaluateHOLFiniteState s (.while c body)).2.memory G')) ∧
    (∀ v, (evaluateHOLFiniteState s (.while c body)).1 = some (.returned v) →
      ∃ G', GIs (evaluateHOLFiniteState s (.while c body)).2.globals G' ∧
        RR v (evaluateHOLFiniteState s (.while c body)).2.memory G') ∧
    (evaluateHOLFiniteState s (.while c body)).1 ≠ some .continue ∧
    (evaluateHOLFiniteState s (.while c body)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · rename_i x hx
    rw [evalHOLFinite_eq_toExact] at hx
    split
    · rename_i nz
      split
      · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩
        all_goals simp_all [Continuing]
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have st := hb F (decClockHOLFinite s) code dom aw sl ⟨pre,hc s x aw dom pre sl hx nz⟩
        have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        cases run : evaluateHOLFiniteState (decClockHOLFinite s) body with
        | mk result middle =>
          rw [run] at st meta' remaining
          obtain ⟨m1,a1,n1,b1,r1,c1⟩ := st
          have smaller : middle.clock < s.clock := by
            change middle.clock ≤ s.clock - 1 at remaining
            omega
          cases result with
          | none =>
            obtain ⟨sl1,i1⟩ := n1 rfl
            obtain ⟨d1,d2,d3⟩ := dom
            have again := aqgd_whileBreak_run c body hc hb middle (meta'.1.trans code)
              ⟨by rw [meta'.2.1]; exact d1,meta'.2.1.trans d2,meta'.2.2.1.trans d3⟩ (a1 (Or.inl rfl)) sl1 i1
            exact ⟨again.1.trans m1,again.2⟩
          | some result =>
            cases result with
            | «continue» => exact absurd rfl c1
            | «break» =>
              obtain ⟨sl1,q1⟩ := b1 rfl
              exact ⟨m1,fun _ => a1 (Or.inr (Or.inr (Or.inl rfl))),fun _ => ⟨sl1,_,rfl,Or.inr q1⟩,
                (fun v e => by cases e),by simp,by simp⟩
            | returned v => exact ⟨m1,a1,(fun e => by cases e),fun v' e => by cases e; exact ⟨_,rfl,r1 v rfl⟩,
                by simp,by simp⟩
            | exception _ _ => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
            | finalFfi _ => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
            | error => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
            | timeOut => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
    · exact ⟨rfl,fun _ => aw,fun _ => ⟨sl,_,rfl,Or.inl pre⟩,(fun v e => by cases e),by simp,by simp⟩
  · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩
    all_goals simp_all [Continuing]
termination_by s.clock

theorem aqgd_whileBreak {I C Qb : GA → Mem → GA → Prop} (c : ExpHOL 64) {body : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), A s.globals → DomD D B s →
      I s.locals s.memory s.globals → SL Vn s.locals → EV s c = some (.val (.word x)) → x ≠ 0 →
      C s.locals s.memory s.globals)
    (hb : AQGB D B A w Vn (fun L M G => I L M G ∧ C L M G) I Qb RR body) :
    AQGD D B A w Vn I (fun L M G => I L M G ∨ Qb L M G) RR (.while c body) := by
  intro F s code dom aw sl G hG pre
  unfold GIs at hG; subst hG
  exact aqgd_whileBreak_run c body hc hb s code dom aw sl pre


theorem aqgd_iteD {P Q CT CF : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} (c : ExpHOL 64)
    {y n : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (H : HolFiniteMapExact MlS (ValueHOL 64)), A s.globals → DomD D B s →
      GIs s.globals H → P s.locals s.memory H → SL Vn s.locals → EV s c = some (.val (.word x)) →
      (x ≠ 0 → CT s.locals s.memory H) ∧ (x = 0 → CF s.locals s.memory H))
    (hy : AQGD D B A w Vn (fun L M H => P L M H ∧ CT L M H) Q RR y)
    (hn : AQGD D B A w Vn (fun L M H => P L M H ∧ CF L M H) Q RR n) :
    AQGD D B A w Vn P Q RR (.ite c y n) := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i x hx
    have cc := hc s x H aw dom hH pre sl hx
    split
    · rename_i z; exact hn F s code dom aw sl H hH ⟨pre,cc.2 z⟩
    · rename_i z; exact hy F s code dom aw sl H hH ⟨pre,cc.1 z⟩
  · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aqgd_decD {P Pb Qb Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} (name : MlS)
    (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} (hshape : Vn name → shape = .one)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v H, A s.globals → DomD D B s → GIs s.globals H → P s.locals s.memory H →
      SL Vn s.locals → EV s init = some v → shapeEqHOL shape (shapeOfHOLExact v) = true →
      Pb (s.locals.update (name,v)) s.memory H)
    (hb : AQGD D B A w Vn Pb Qb RR body)
    (hq : ∀ L M H L' M' H', P L M H → Qb L' M' H' → Q (L'.resVarEq (name,L.lookup name)) M' H') :
    AQGD D B A w Vn P Q RR (.dec name shape init body) := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · rename_i v hv
    split
    · rename_i hs
      have slb : SL Vn (setVarHOLFinite name v s).locals :=
        sl_update sl name v (fun hn => by rw [hshape hn] at hs; exact scalar_of_shape hs)
      obtain ⟨m1,a1,n1,r1,c1,b1⟩ := hb F (setVarHOLFinite name v s) (by exact code) (by exact dom) (by exact aw) slb
        H (by exact hH) (hi s v H aw dom hH pre sl hv hs)
      refine ⟨m1,a1,fun e => ?_,r1,c1,b1⟩
      obtain ⟨sl1,H',hH',q1⟩ := n1 e
      exact ⟨sl_restore sl1 sl name,H',hH',hq _ _ _ _ _ _ pre q1⟩
    · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aqgd_returnD {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} (e : ExpHOL 64)
    (hr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v H, A s.globals → DomD D B s → GIs s.globals H → P s.locals s.memory H →
      SL Vn s.locals → EV s e = some v → RR v s.memory H) :
    AQGD D B A w Vn P Q RR (.return e) := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_return]
  split
  · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · rename_i v hv
    split
    · refine ⟨rfl,fun _ => aw,(fun e => by cases e),fun v' e => ?_,by simp,by simp⟩
      simp only [Option.some.injEq,PanSemResultExact.returned.injEq] at e
      subst e
      exact ⟨H,hH,hr s v H aw dom hH pre sl hv⟩
    · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aqgd_storeD {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) H, A s.globals → DomD D B s → GIs s.globals H → P s.locals s.memory H →
      SL Vn s.locals → ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ w ≠ a ∧
        ∀ y : BitVec 64, EV s v = some (.val (.word y)) →
          Q s.locals (fun x => if x = a then .word y else s.memory x) H)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x H, A s.globals → DomD D B s → GIs s.globals H → P s.locals s.memory H →
      SL Vn s.locals → EV s v = some x → ∃ y : BitVec 64, x = .val (.word y)) :
    AQGD D B A w Vn P Q RR (.store d v) := by
  intro F s code dom aw sl H hH pre
  obtain ⟨a,ha,ne,hq⟩ := hd s H aw dom hH pre sl
  obtain ⟨res,_,loc,glob,mem⟩ := evaluate_store_word_frame s d v a ha (hv s · H aw dom hH pre sl)
  refine ⟨mem w ne,fun _ => by rw [glob]; exact aw,fun e => ⟨by rw [loc]; exact sl,H,by unfold GIs; rw [glob]; exact hH,?_⟩,?_,?_,?_⟩
  · cases hvv : EV s v with
    | none =>
      exfalso
      rw [evaluateHOLFiniteState_store] at e
      simp only [EV] at ha hvv
      rw [ha] at e
      dsimp only at e
      rw [hvv] at e
      cases e
    | some x =>
      obtain ⟨y,rfl⟩ := hv s x H aw dom hH pre sl hvv
      rw [loc,store_none_mem s d v a y ha hvv e]
      exact hq y hvv
  · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
  all_goals rcases res with h | h <;> rw [h] <;> simp


#print axioms aqgd_whileBreak
#print axioms aqgb_seq
end InitECandidate.Runtime
