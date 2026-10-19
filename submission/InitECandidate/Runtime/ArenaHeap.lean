import InitECandidate.Runtime.TxEntryPreState
import InitECandidate.Runtime.HtabSetLayArena
/-!
Heap-aware arena triple `AQMH`.  With `AQM` the arena lower bound `P0` is fixed
for the whole triple, so objects allocated inside a call (grown table arrays)
cannot be named as "below the current heap" by later frames.  `AQMH` threads the
actual heap-pointer value through pre/post assertions; `aqmh_of_aqm` lifts any
existing `AQM` proof (instantiated at the entry heap) and the call rules compose
heap-aware callee specs.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The heap pointer of a globals map. -/
def HeapIs (g : HolFiniteMapExact MlS (ValueHOL 64)) (H : BitVec 64) : Prop :=
  g.lookup (ofString "heap_ptr") = some (.val (.word H))

/-- Heap-aware memory-aware arena triple: assertions also see the heap pointer. -/
def AQMH (SP0 P0 FM : BitVec 64) (G0 : HolFiniteMapExact MlS (ValueHOL 64)) (w : BitVec 64) (Vn : MlS → Prop)
    (P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop) (RR : ValueHOL 64 → Mem → BitVec 64 → Prop)
    (p : ProgHOL 64) : Prop :=
  ∀ (F : Type) (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomOK s.memaddrs →
    AW SP0 P0 FM G0 s.globals → SL Vn s.locals → ∀ H, HeapIs s.globals H → P s.locals s.memory H →
    (evaluateHOLFiniteState s p).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s p).1 → AW SP0 P0 FM G0 (evaluateHOLFiniteState s p).2.globals) ∧
    ((evaluateHOLFiniteState s p).1 = none → SL Vn (evaluateHOLFiniteState s p).2.locals ∧
      ∃ H', HeapIs (evaluateHOLFiniteState s p).2.globals H' ∧
        Q (evaluateHOLFiniteState s p).2.locals (evaluateHOLFiniteState s p).2.memory H') ∧
    (∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) →
      ∃ H', HeapIs (evaluateHOLFiniteState s p).2.globals H' ∧ RR v (evaluateHOLFiniteState s p).2.memory H') ∧
    (evaluateHOLFiniteState s p).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p).1 ≠ some .break

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}

/-- Raising the arena lower bound to the current heap pointer keeps the arena globals. -/
theorem aw_raise {g : HolFiniteMapExact MlS (ValueHOL 64)} (aw : AW SP0 P0 FM G0 g) {H : BitVec 64}
    (hH : HeapIs g H) : AW SP0 H FM G0 g ∧ P0.toNat ≤ H.toNat := by
  obtain ⟨hf,hs,⟨h,hh,lo,hi,al⟩,st⟩ := aw
  rw [hH] at hh
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hh
  subst hh
  exact ⟨⟨hf,hs,⟨H,hH,le_refl _,hi,al⟩,st⟩,lo⟩

theorem aw_lower {g : HolFiniteMapExact MlS (ValueHOL 64)} {H : BitVec 64} (aw : AW SP0 H FM G0 g)
    (le : P0.toNat ≤ H.toNat) : AW SP0 P0 FM G0 g ∧ ∃ H', HeapIs g H' ∧ H.toNat ≤ H'.toNat := by
  obtain ⟨hf,hs,⟨h,hh,lo,hi,al⟩,st⟩ := aw
  exact ⟨⟨hf,hs,⟨h,hh,by omega,hi,al⟩,st⟩,h,hh,lo⟩

/-- Lifting: a memory-aware triple proven at every lower bound at least `P0` gives a heap-aware triple, run at the
entry heap pointer, whose exit heap pointer is at least the entry one. -/
theorem aqmh_of_aqm {P Q : BitVec 64 → HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop}
    {RR : BitVec 64 → ValueHOL 64 → Mem → Prop} {p : ProgHOL 64}
    (h : ∀ H : BitVec 64, P0.toNat ≤ H.toNat → AQM SP0 H FM G0 w Vn (P H) (Q H) (RR H) p) :
    AQMH SP0 P0 FM G0 w Vn (fun L M H => P H L M)
      (fun L M H' => ∃ H : BitVec 64, P0.toNat ≤ H.toNat ∧ H.toNat ≤ H'.toNat ∧ Q H L M)
      (fun v M H' => ∃ H : BitVec 64, P0.toNat ≤ H.toNat ∧ H.toNat ≤ H'.toNat ∧ RR H v M) p := by
  intro F s code dom aw sl H hH pre
  obtain ⟨awH,le⟩ := aw_raise aw hH
  obtain ⟨m,a,n,r,c,b⟩ := h H le F s code dom awH sl pre
  refine ⟨m,fun cont => (aw_lower (a cont) le).1,fun e => ?_,fun v e => ?_,c,b⟩
  · obtain ⟨_,H',hH',le'⟩ := aw_lower (a (Or.inl e)) le
    exact ⟨(n e).1,H',hH',H,le,le',(n e).2⟩
  · obtain ⟨_,H',hH',le'⟩ := aw_lower (a (Or.inr (Or.inr (Or.inr ⟨v,e⟩)))) le
    exact ⟨H',hH',H,le,le',r v e⟩


variable {RR : ValueHOL 64 → Mem → BitVec 64 → Prop}

theorem aqmh_of_nc {Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop} {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)} (m : t.memory w = s.memory w)
    (h : ¬ Continuing r) :
    (r,t).2.memory w = s.memory w ∧ (Continuing (r,t).1 → AW SP0 P0 FM G0 (r,t).2.globals) ∧
      ((r,t).1 = none → SL Vn (r,t).2.locals ∧ ∃ H', HeapIs (r,t).2.globals H' ∧ Q (r,t).2.locals (r,t).2.memory H') ∧
      (∀ v, (r,t).1 = some (.returned v) → ∃ H', HeapIs (r,t).2.globals H' ∧ RR v (r,t).2.memory H') ∧
      (r,t).1 ≠ some .continue ∧ (r,t).1 ≠ some .break :=
  ⟨m,fun c => absurd c h,fun e => absurd (Or.inl e) h,fun v e => absurd (Or.inr (Or.inr (Or.inr ⟨v,e⟩))) h,
    fun e => h (Or.inr (Or.inl e)),fun e => h (Or.inr (Or.inr (Or.inl e)))⟩

theorem aqmh_conseq {P P' Q Q' : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop}
    {RR' : ValueHOL 64 → Mem → BitVec 64 → Prop} {p : ProgHOL 64}
    (h : AQMH SP0 P0 FM G0 w Vn P Q RR p) (hp : ∀ L M H, P' L M H → P L M H) (hq : ∀ L M H, Q L M H → Q' L M H)
    (hr : ∀ v M H, RR v M H → RR' v M H) : AQMH SP0 P0 FM G0 w Vn P' Q' RR' p := by
  intro F s code dom aw sl H hH pre
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl H hH (hp _ _ _ pre)
  refine ⟨m,a,fun e => ?_,fun v e => ?_,c,b⟩
  · obtain ⟨sl',H',h1,h2⟩ := n e; exact ⟨sl',H',h1,hq _ _ _ h2⟩
  · obtain ⟨H',h1,h2⟩ := r v e; exact ⟨H',h1,hr _ _ _ h2⟩

theorem aqmh_seq {P Q R : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop} {p q : ProgHOL 64}
    (hp : AQMH SP0 P0 FM G0 w Vn P Q RR p) (hq : AQMH SP0 P0 FM G0 w Vn Q R RR q) :
    AQMH SP0 P0 FM G0 w Vn P R RR (.seq p q) := by
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

theorem aqmh_ite {P Q CT CF : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop} (c : ExpHOL 64)
    {y n : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (H : BitVec 64), AW SP0 P0 FM G0 s.globals →
      P s.locals s.memory H → SL Vn s.locals → EV s c = some (.val (.word x)) →
      (x ≠ 0 → CT s.locals s.memory H) ∧ (x = 0 → CF s.locals s.memory H))
    (hy : AQMH SP0 P0 FM G0 w Vn (fun L M H => P L M H ∧ CT L M H) Q RR y)
    (hn : AQMH SP0 P0 FM G0 w Vn (fun L M H => P L M H ∧ CF L M H) Q RR n) :
    AQMH SP0 P0 FM G0 w Vn P Q RR (.ite c y n) := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i x hx
    have cc := hc s x H aw pre sl hx
    split
    · rename_i z; exact hn F s code dom aw sl H hH ⟨pre,cc.2 z⟩
    · rename_i z; exact hy F s code dom aw sl H hH ⟨pre,cc.1 z⟩
  · exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aqmh_dec {P Pb Qb Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop} (name : MlS)
    (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} (hshape : Vn name → shape = .one)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v H, AW SP0 P0 FM G0 s.globals → P s.locals s.memory H →
      SL Vn s.locals → EV s init = some v → shapeEqHOL shape (shapeOfHOLExact v) = true →
      Pb (s.locals.update (name,v)) s.memory H)
    (hb : AQMH SP0 P0 FM G0 w Vn Pb Qb RR body)
    (hq : ∀ L M H L' M' H', P L M H → Qb L' M' H' → Q (L'.resVarEq (name,L.lookup name)) M' H') :
    AQMH SP0 P0 FM G0 w Vn P Q RR (.dec name shape init body) := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · rename_i v hv
    split
    · rename_i hs
      have slb : SL Vn (setVarHOLFinite name v s).locals :=
        sl_update sl name v (fun hn => by rw [hshape hn] at hs; exact scalar_of_shape hs)
      obtain ⟨m1,a1,n1,r1,c1,b1⟩ := hb F (setVarHOLFinite name v s) (by exact code) (by exact dom) (by exact aw) slb
        H (by exact hH) (hi s v H aw pre sl hv hs)
      refine ⟨m1,a1,fun e => ?_,r1,c1,b1⟩
      obtain ⟨sl1,H',hH',q1⟩ := n1 e
      exact ⟨sl_restore sl1 sl name,H',hH',hq _ _ _ _ _ _ pre q1⟩
    · exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aqmh_return {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop} (e : ExpHOL 64)
    (hr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v H, AW SP0 P0 FM G0 s.globals → P s.locals s.memory H →
      SL Vn s.locals → EV s e = some v → RR v s.memory H) :
    AQMH SP0 P0 FM G0 w Vn P Q RR (.return e) := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_return]
  split
  · exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · rename_i v hv
    split
    · refine ⟨rfl,fun _ => aw,(fun e => by cases e),fun v' e => ?_,by simp,by simp⟩
      simp only [Option.some.injEq,PanSemResultExact.returned.injEq] at e
      subst e
      exact ⟨H,hH,hr s v H aw pre sl hv⟩
    · exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- Spec-based calls. -/
theorem aqmh_callSpec {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop} {Vn' : MlS → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → ValueHOL 64 → Mem → BitVec 64 → Prop)
    (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQMH SP0 P0 FM G0 w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, AW SP0 P0 FM G0 s.globals →
      ∀ H, HeapIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hq : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → Q L M' H') :
    AQMH SP0 P0 FM G0 w Vn P Q RR (.call (some (none,none)) function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
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
      · exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
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
            | exact aqmh_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- A declared call against a callee spec. -/
theorem aqmh_decCallSpec {P Pc Qc Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop} {Vn' : MlS → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → ValueHOL 64 → Mem → BitVec 64 → Prop)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQMH SP0 P0 FM G0 w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, AW SP0 P0 FM G0 s.globals →
      ∀ H, HeapIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hshape : Vn name → shape = .one)
    (hret : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → shapeEqHOL (shapeOfHOLExact v) shape = true →
      Pc (L.update (name,v)) M' H')
    (hc : AQMH SP0 P0 FM G0 w Vn Pc Qc RR cont)
    (hq : ∀ L M H L' M' H', P L M H → Qc L' M' H' → Q (L'.resVarEq (name,L.lookup name)) M' H') :
    AQMH SP0 P0 FM G0 w Vn P Q RR (.decCall name shape function arguments cont) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_decCall_total]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
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
      · exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
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
          | none => exact aqmh_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
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
              · exact aqmh_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
            | _ => exact aqmh_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)


#print axioms aqmh_of_aqm
#print axioms aqmh_callSpec
#print axioms aqmh_decCallSpec
#print axioms aqmh_seq
#print axioms aqmh_dec
end InitECandidate.Runtime
