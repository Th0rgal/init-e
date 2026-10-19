import InitECandidate.Runtime.ArenaHeapG
import InitECandidate.Runtime.HtabSpecArena
import InitECandidate.Runtime.HtabSetBound
/-!
`AQG A`: the memory-aware triple whose assertions see the whole globals map (instead of only the heap pointer), over
an arbitrary arena predicate `A` kept on continuing outcomes; obtained from `AQG` by replacing "the heap pointer is
`H`" with "the globals are `G`".
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The globals map is `G`. -/
def GIs (g G : HolFiniteMapExact MlS (ValueHOL 64)) : Prop := g = G

/-- `AQMH` over an arbitrary arena predicate `A` on the globals (kept on continuing outcomes). -/
def AQG (A : HolFiniteMapExact MlS (ValueHOL 64) → Prop) (w : BitVec 64) (Vn : MlS → Prop)
    (P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop) (RR : ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (p : ProgHOL 64) : Prop :=
  ∀ (F : Type) (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomOK s.memaddrs →
    A s.globals → SL Vn s.locals → ∀ H, GIs s.globals H → P s.locals s.memory H →
    (evaluateHOLFiniteState s p).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s p).1 → A (evaluateHOLFiniteState s p).2.globals) ∧
    ((evaluateHOLFiniteState s p).1 = none → SL Vn (evaluateHOLFiniteState s p).2.locals ∧
      ∃ H', GIs (evaluateHOLFiniteState s p).2.globals H' ∧
        Q (evaluateHOLFiniteState s p).2.locals (evaluateHOLFiniteState s p).2.memory H') ∧
    (∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) →
      ∃ H', GIs (evaluateHOLFiniteState s p).2.globals H' ∧ RR v (evaluateHOLFiniteState s p).2.memory H') ∧
    (evaluateHOLFiniteState s p).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p).1 ≠ some .break

variable {A : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {w : BitVec 64} {Vn : MlS → Prop}

variable {RR : ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}

theorem aqg_of_nc {Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)} (m : t.memory w = s.memory w)
    (h : ¬ Continuing r) :
    (r,t).2.memory w = s.memory w ∧ (Continuing (r,t).1 → A (r,t).2.globals) ∧
      ((r,t).1 = none → SL Vn (r,t).2.locals ∧ ∃ H', GIs (r,t).2.globals H' ∧ Q (r,t).2.locals (r,t).2.memory H') ∧
      (∀ v, (r,t).1 = some (.returned v) → ∃ H', GIs (r,t).2.globals H' ∧ RR v (r,t).2.memory H') ∧
      (r,t).1 ≠ some .continue ∧ (r,t).1 ≠ some .break :=
  ⟨m,fun c => absurd c h,fun e => absurd (Or.inl e) h,fun v e => absurd (Or.inr (Or.inr (Or.inr ⟨v,e⟩))) h,
    fun e => h (Or.inr (Or.inl e)),fun e => h (Or.inr (Or.inr (Or.inl e)))⟩

theorem aqg_conseq {P P' Q Q' : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    {RR' : ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {p : ProgHOL 64}
    (h : AQG A w Vn P Q RR p) (hp : ∀ L M H, P' L M H → P L M H) (hq : ∀ L M H, Q L M H → Q' L M H)
    (hr : ∀ v M H, RR v M H → RR' v M H) : AQG A w Vn P' Q' RR' p := by
  intro F s code dom aw sl H hH pre
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl H hH (hp _ _ _ pre)
  refine ⟨m,a,fun e => ?_,fun v e => ?_,c,b⟩
  · obtain ⟨sl',H',h1,h2⟩ := n e; exact ⟨sl',H',h1,hq _ _ _ h2⟩
  · obtain ⟨H',h1,h2⟩ := r v e; exact ⟨H',h1,hr _ _ _ h2⟩

theorem aqg_seq {P Q R : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {p q : ProgHOL 64}
    (hp : AQG A w Vn P Q RR p) (hq : AQG A w Vn Q R RR q) :
    AQG A w Vn P R RR (.seq p q) := by
  intro F s code dom aw sl H hH pre
  have h1 := hp F s code dom aw sl H hH pre
  have meta' := evaluateHOLFiniteState_metadata s p
  rw [evaluateHOLFiniteState_seq_line780]
  cases r : evaluateHOLFiniteState s p with
  | mk res m =>
    rw [r] at h1 meta'
    obtain ⟨m1,a1,n1,r1,c1,b1⟩ := h1
    cases res with
    | some x => exact ⟨m1,a1,(fun e => by cases e),r1,c1,b1⟩
    | none =>
      obtain ⟨sl1,H1,hH1,q1⟩ := n1 rfl
      obtain ⟨m2,a2,n2,r2,c2,b2⟩ := hq F m (meta'.1.trans code) (by rw [meta'.2.1]; exact dom) (a1 (Or.inl rfl)) sl1
        H1 hH1 q1
      exact ⟨m2.trans m1,a2,n2,r2,c2,b2⟩

theorem aqg_ite {P Q CT CF : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} (c : ExpHOL 64)
    {y n : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (H : HolFiniteMapExact MlS (ValueHOL 64)), A s.globals →
      GIs s.globals H → P s.locals s.memory H → SL Vn s.locals → EV s c = some (.val (.word x)) →
      (x ≠ 0 → CT s.locals s.memory H) ∧ (x = 0 → CF s.locals s.memory H))
    (hy : AQG A w Vn (fun L M H => P L M H ∧ CT L M H) Q RR y)
    (hn : AQG A w Vn (fun L M H => P L M H ∧ CF L M H) Q RR n) :
    AQG A w Vn P Q RR (.ite c y n) := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i x hx
    have cc := hc s x H aw hH pre sl hx
    split
    · rename_i z; exact hn F s code dom aw sl H hH ⟨pre,cc.2 z⟩
    · rename_i z; exact hy F s code dom aw sl H hH ⟨pre,cc.1 z⟩
  · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aqg_dec {P Pb Qb Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} (name : MlS)
    (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} (hshape : Vn name → shape = .one)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v H, A s.globals → GIs s.globals H → P s.locals s.memory H →
      SL Vn s.locals → EV s init = some v → shapeEqHOL shape (shapeOfHOLExact v) = true →
      Pb (s.locals.update (name,v)) s.memory H)
    (hb : AQG A w Vn Pb Qb RR body)
    (hq : ∀ L M H L' M' H', P L M H → Qb L' M' H' → Q (L'.resVarEq (name,L.lookup name)) M' H') :
    AQG A w Vn P Q RR (.dec name shape init body) := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · rename_i v hv
    split
    · rename_i hs
      have slb : SL Vn (setVarHOLFinite name v s).locals :=
        sl_update sl name v (fun hn => by rw [hshape hn] at hs; exact scalar_of_shape hs)
      obtain ⟨m1,a1,n1,r1,c1,b1⟩ := hb F (setVarHOLFinite name v s) (by exact code) (by exact dom) (by exact aw) slb
        H (by exact hH) (hi s v H aw hH pre sl hv hs)
      refine ⟨m1,a1,fun e => ?_,r1,c1,b1⟩
      obtain ⟨sl1,H',hH',q1⟩ := n1 e
      exact ⟨sl_restore sl1 sl name,H',hH',hq _ _ _ _ _ _ pre q1⟩
    · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aqg_return {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} (e : ExpHOL 64)
    (hr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v H, A s.globals → GIs s.globals H → P s.locals s.memory H →
      SL Vn s.locals → EV s e = some v → RR v s.memory H) :
    AQG A w Vn P Q RR (.return e) := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_return]
  split
  · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · rename_i v hv
    split
    · refine ⟨rfl,fun _ => aw,(fun e => by cases e),fun v' e => ?_,by simp,by simp⟩
      simp only [Option.some.injEq,PanSemResultExact.returned.injEq] at e
      subst e
      exact ⟨H,hH,hr s v H aw hH pre sl hv⟩
    · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- Spec-based calls. -/
theorem aqg_callSpec {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {Vn' : MlS → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQG A w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hq : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → Q L M' H') :
    AQG A w Vn P Q RR (.call (some (none,none)) function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      have esl := callee_entry_sl function values parameters found returnShape installed allOne found callee foundShape
        lookup'
      split
      · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (sl_mono esl (fun _ _ => trivial)) H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals first
            | (obtain ⟨H',hH',rr⟩ := r1 _ rfl
               exact ⟨m1,fun _ => a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),fun _ => ⟨sl,H',hH',hq _ _ _ _ _ _ pre rr⟩,
                (fun v e => by cases e),by simp,by simp⟩)
            | exact aqg_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- A declared call against a callee spec. -/
theorem aqg_decCallSpec {P Pc Qc Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {Vn' : MlS → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQG A w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hshape : Vn name → shape = .one)
    (hret : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → shapeEqHOL (shapeOfHOLExact v) shape = true →
      Pc (L.update (name,v)) M' H')
    (hc : AQG A w Vn Pc Qc RR cont)
    (hq : ∀ L M H L' M' H', P L M H → Qc L' M' H' → Q (L'.resVarEq (name,L.lookup name)) M' H') :
    AQG A w Vn P Q RR (.decCall name shape function arguments cont) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_decCall_total]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      have esl := callee_entry_sl function values parameters found returnShape installed allOne found callee foundShape
        lookup'
      split
      · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (sl_mono esl (fun _ _ => trivial)) H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame meta'
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          dsimp only [fixClockHOLFinite]
          cases rb with
          | none => exact aqg_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · rename_i ok
                simp only [Bool.and_eq_true] at ok
                have cslx : SL Vn (state.locals.update (name,v)) :=
                  sl_update sl name v (fun hn => by rw [hshape hn] at ok; exact scalar_of_shape' ok.1)
                obtain ⟨H',hH',rr⟩ := r1 v rfl
                have pc := hret _ _ _ _ _ _ pre rr ok.1
                obtain ⟨m2,a2,n2,r2,c2,b2⟩ := hc F (setVarHOLFinite name v { bodyPost with clock := _, locals := state.locals })
                  (by exact meta'.1.trans code) (by intro a ha; exact dom a (meta'.2.1 ▸ ha))
                  (by exact a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))) cslx H' (by exact hH') pc
                refine ⟨m2.trans m1,a2,fun e => ?_,r2,c2,b2⟩
                obtain ⟨sl2,H2,hH2,q2⟩ := n2 e
                exact ⟨sl_restore sl2 sl name,H2,hH2,hq _ _ _ _ _ _ pre q2⟩
              · exact aqg_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
            | _ => exact aqg_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)


#print axioms aqg_callSpec
#print axioms aqg_decCallSpec
#print axioms aqg_seq
#print axioms aqg_dec

theorem aqg_skip {P : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} :
    AQG A w Vn P P RR .skip := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_skip]
  exact ⟨rfl,fun _ => aw,fun _ => ⟨sl,H,hH,pre⟩,(fun v e => by cases e),by simp,by simp⟩

theorem aqg_false {Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {p : ProgHOL 64} :
    AQG A w Vn (fun _ _ _ => False) Q RR p := fun _ _ _ _ _ _ _ _ pre => pre.elim

theorem aqg_raise {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} (eid : MlS) (e : ExpHOL 64) :
    AQG A w Vn P Q RR (.raise eid e) := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- A word store: the normal postcondition sees the stored word at the same heap pointer. -/
theorem aqg_store {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) H, A s.globals → GIs s.globals H → P s.locals s.memory H →
      SL Vn s.locals → ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ w ≠ a ∧
        ∀ y : BitVec 64, EV s v = some (.val (.word y)) →
          Q s.locals (fun x => if x = a then .word y else s.memory x) H)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x H, A s.globals → GIs s.globals H → P s.locals s.memory H →
      SL Vn s.locals → EV s v = some x → ∃ y : BitVec 64, x = .val (.word y)) :
    AQG A w Vn P Q RR (.store d v) := by
  intro F s code dom aw sl H hH pre
  obtain ⟨a,ha,ne,hq⟩ := hd s H aw hH pre sl
  obtain ⟨res,_,loc,glob,mem⟩ := evaluate_store_word_frame s d v a ha (hv s · H aw hH pre sl)
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
      obtain ⟨y,rfl⟩ := hv s x H aw hH pre sl hvv
      rw [loc,store_none_mem s d v a y ha hvv e]
      exact hq y hvv
  · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
  all_goals rcases res with h | h <;> rw [h] <;> simp

/-- A read-only body (memory and globals kept in every outcome) as a callee spec. -/
theorem aqg_of_mf {body : ProgHOL 64} (hmf : MemoryFrame body) (nb : noTopBreak body = true)
    (nc : noTopContinue body = true) (M0 : Mem) (H0 : HolFiniteMapExact MlS (ValueHOL 64)) :
    AQG A w (fun _ => False) (fun _ M H => M = M0 ∧ H = H0) (fun _ _ _ => True)
      (fun _ M H => M = M0 ∧ H = H0) body := by
  intro F s code dom aw sl H hH ⟨hm,he⟩
  obtain ⟨m,g⟩ := hmf s code
  refine ⟨by rw [m],fun _ => by rw [g]; exact aw,fun _ => ⟨fun _ h => h.elim,H,by unfold GIs; rw [g]; exact hH,trivial⟩,
    fun v _ => ⟨H,by unfold GIs; rw [g]; exact hH,by rw [m]; exact hm,he⟩,
    evaluate_noTopContinue body nc s,evaluate_noTopBreak body nb s⟩

/-- Strengthening the arena predicate by a global fact that the program keeps on continuing outcomes. -/
theorem aqg_strengthen {X : HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {p : ProgHOL 64}
    (h : AQG A w Vn P Q RR p)
    (keep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → X s.globals →
      X (evaluateHOLFiniteState s p).2.globals) :
    AQG (fun g => A g ∧ X g) w Vn P Q RR p := by
  intro F s code dom ⟨aw,x⟩ sl H hH pre
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl H hH pre
  exact ⟨m,fun cont => ⟨a cont,keep s code x⟩,n,r,c,b⟩

theorem aqg_weaken {X : HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {p : ProgHOL 64}
    (h : AQG (fun g => A g ∧ X g) w Vn P Q RR p) (hx : ∀ g, A g → X g) : AQG A w Vn P Q RR p :=
  fun F s code dom aw sl H hH pre => by
    obtain ⟨m,a,n,r,c,b⟩ := h F s code dom ⟨aw,hx _ aw⟩ sl H hH pre
    exact ⟨m,fun cont => (a cont).1,n,r,c,b⟩


/-- A global assignment: the arena predicate and postcondition are checked on the updated globals. -/
theorem aqg_assignGlobal {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    (name : MlS) (e : ExpHOL 64)
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, A s.globals → P s.locals s.memory s.globals →
      SL Vn s.locals → EV s e = some v →
      A (setGlobalHOLFinite name v s).globals ∧ Q s.locals s.memory (setGlobalHOLFinite name v s).globals) :
    AQG A w Vn P Q RR (.assign .global name e) := by
  intro F s code dom aw sl H hH pre
  unfold GIs at hH; subst hH
  rw [evaluateHOLFiniteState_assign]
  split
  · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · rename_i v hv
    split
    · obtain ⟨a,q⟩ := h s v aw pre sl hv
      exact ⟨rfl,fun _ => a,fun _ => ⟨sl,_,rfl,q⟩,(fun v e => by cases e),by simp,by simp⟩
    · exact aqg_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- Lifting a heap-aware triple: the pre/post see the heap pointer of the globals map, and a global fact `R` kept
by the program is carried from entry to every exit. -/
theorem aqg_of_aqmg {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop}
    {RR' : ValueHOL 64 → Mem → BitVec 64 → Prop} {p : ProgHOL 64} (h : AQMG A w Vn P Q RR' p)
    (R : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (keep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → R s.globals →
      R (evaluateHOLFiniteState s p).2.globals) :
    AQG A w Vn (fun L M G => R G ∧ ∃ H, HeapIs G H ∧ P L M H) (fun L M G => R G ∧ ∃ H, HeapIs G H ∧ Q L M H)
      (fun v M G => R G ∧ ∃ H, HeapIs G H ∧ RR' v M H) p := by
  intro F s code dom aw sl G hG ⟨r,H,hH,pre⟩
  unfold GIs at hG; subst hG
  obtain ⟨m,a,n,rr,c,b⟩ := h F s code dom aw sl H hH pre
  refine ⟨m,a,fun e => ?_,fun v e => ?_,c,b⟩
  · obtain ⟨sl',H',h1,h2⟩ := n e
    exact ⟨sl',_,rfl,keep s code r,H',h1,h2⟩
  · obtain ⟨H',h1,h2⟩ := rr v e
    exact ⟨_,rfl,keep s code r,H',h1,h2⟩

#print axioms aqg_assignGlobal
#print axioms aqg_of_aqmg
end InitECandidate.Runtime
