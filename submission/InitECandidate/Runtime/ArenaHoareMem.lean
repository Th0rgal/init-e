import InitECandidate.Runtime.AccountOptionalArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Word memories. -/
abbrev Mem := BitVec 64 → HolWordLab 64

/-- Memory-aware arena triple: preconditions and normal postconditions see the locals and the whole memory; a
returned outcome satisfies `RR` on the returned value and the final memory. The watched word is kept in every
outcome and the arena globals on continuing outcomes, and no `break` or `continue` escapes. -/
def AQM (SP0 P0 FM : BitVec 64) (G0 : HolFiniteMapExact MlS (ValueHOL 64)) (w : BitVec 64) (Vn : MlS → Prop)
    (P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop) (RR : ValueHOL 64 → Mem → Prop) (p : ProgHOL 64) :
    Prop :=
  ∀ (F : Type) (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomOK s.memaddrs →
    AW SP0 P0 FM G0 s.globals → SL Vn s.locals → P s.locals s.memory →
    (evaluateHOLFiniteState s p).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s p).1 → AW SP0 P0 FM G0 (evaluateHOLFiniteState s p).2.globals) ∧
    ((evaluateHOLFiniteState s p).1 = none → SL Vn (evaluateHOLFiniteState s p).2.locals ∧
      Q (evaluateHOLFiniteState s p).2.locals (evaluateHOLFiniteState s p).2.memory) ∧
    (∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) → RR v (evaluateHOLFiniteState s p).2.memory) ∧
    (evaluateHOLFiniteState s p).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p).1 ≠ some .break

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → Prop}

theorem aqm_of_nc {Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)} (m : t.memory w = s.memory w)
    (h : ¬ Continuing r) :
    (r,t).2.memory w = s.memory w ∧ (Continuing (r,t).1 → AW SP0 P0 FM G0 (r,t).2.globals) ∧
      ((r,t).1 = none → SL Vn (r,t).2.locals ∧ Q (r,t).2.locals (r,t).2.memory) ∧
      (∀ v, (r,t).1 = some (.returned v) → RR v (r,t).2.memory) ∧ (r,t).1 ≠ some .continue ∧
      (r,t).1 ≠ some .break :=
  ⟨m,fun c => absurd c h,fun e => absurd (Or.inl e) h,fun v e => absurd (Or.inr (Or.inr (Or.inr ⟨v,e⟩))) h,
    fun e => h (Or.inr (Or.inl e)),fun e => h (Or.inr (Or.inr (Or.inl e)))⟩

theorem aqm_conseq {P P' Q Q' : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} {RR' : ValueHOL 64 → Mem → Prop}
    {p : ProgHOL 64} (h : AQM SP0 P0 FM G0 w Vn P Q RR p) (hp : ∀ L M, P' L M → P L M) (hq : ∀ L M, Q L M → Q' L M)
    (hr : ∀ v M, RR v M → RR' v M) : AQM SP0 P0 FM G0 w Vn P' Q' RR' p := by
  intro F s code dom aw sl pre
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl (hp _ _ pre)
  exact ⟨m,a,fun e => ⟨(n e).1,hq _ _ (n e).2⟩,fun v e => hr _ _ (r v e),c,b⟩

theorem aqm_seq {P Q R : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} {p q : ProgHOL 64}
    (hp : AQM SP0 P0 FM G0 w Vn P Q RR p) (hq : AQM SP0 P0 FM G0 w Vn Q R RR q) :
    AQM SP0 P0 FM G0 w Vn P R RR (.seq p q) := by
  intro F s code dom aw sl pre
  have h1 := hp F s code dom aw sl pre
  have meta' := evaluateHOLFiniteState_metadata s p
  rw [evaluateHOLFiniteState_seq_line780]
  cases r : evaluateHOLFiniteState s p with
  | mk res m =>
    rw [r] at h1 meta'
    obtain ⟨m1,a1,n1,r1,c1,b1⟩ := h1
    cases res with
    | some x => exact ⟨m1,a1,(fun e => by cases e),r1,c1,b1⟩
    | none =>
      obtain ⟨sl1,q1⟩ := n1 rfl
      obtain ⟨m2,a2,n2,r2,c2,b2⟩ := hq F m (meta'.1.trans code) (by rw [meta'.2.1]; exact dom) (a1 (Or.inl rfl)) sl1 q1
      exact ⟨m2.trans m1,a2,n2,r2,c2,b2⟩

theorem aqm_skip {P : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} : AQM SP0 P0 FM G0 w Vn P P RR .skip := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_skip]
  exact ⟨rfl,fun _ => aw,fun _ => ⟨sl,pre⟩,(fun v e => by cases e),by simp,by simp⟩

theorem aqm_ite {P Q CT CF : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} (c : ExpHOL 64) {y n : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), AW SP0 P0 FM G0 s.globals →
      P s.locals s.memory → SL Vn s.locals → EV s c = some (.val (.word x)) →
      (x ≠ 0 → CT s.locals s.memory) ∧ (x = 0 → CF s.locals s.memory))
    (hy : AQM SP0 P0 FM G0 w Vn (fun L M => P L M ∧ CT L M) Q RR y)
    (hn : AQM SP0 P0 FM G0 w Vn (fun L M => P L M ∧ CF L M) Q RR n) :
    AQM SP0 P0 FM G0 w Vn P Q RR (.ite c y n) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i x hx
    have cc := hc s x aw pre sl hx
    split
    · rename_i z; exact hn F s code dom aw sl ⟨pre,cc.2 z⟩
    · rename_i z; exact hy F s code dom aw sl ⟨pre,cc.1 z⟩
  · exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aqm_while_run {I C : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} (c : ExpHOL 64) (body : ProgHOL 64)
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), AW SP0 P0 FM G0 s.globals →
      I s.locals s.memory → SL Vn s.locals → EV s c = some (.val (.word x)) → x ≠ 0 → C s.locals s.memory)
    (hb : AQM SP0 P0 FM G0 w Vn (fun L M => I L M ∧ C L M) I RR body) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode) (dom : DomOK s.memaddrs)
    (aw : AW SP0 P0 FM G0 s.globals) (sl : SL Vn s.locals) (pre : I s.locals s.memory) :
    (evaluateHOLFiniteState s (.while c body)).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s (.while c body)).1 →
      AW SP0 P0 FM G0 (evaluateHOLFiniteState s (.while c body)).2.globals) ∧
    ((evaluateHOLFiniteState s (.while c body)).1 = none → SL Vn (evaluateHOLFiniteState s (.while c body)).2.locals ∧
      I (evaluateHOLFiniteState s (.while c body)).2.locals (evaluateHOLFiniteState s (.while c body)).2.memory) ∧
    (∀ v, (evaluateHOLFiniteState s (.while c body)).1 = some (.returned v) →
      RR v (evaluateHOLFiniteState s (.while c body)).2.memory) ∧
    (evaluateHOLFiniteState s (.while c body)).1 ≠ some .continue ∧
    (evaluateHOLFiniteState s (.while c body)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · rename_i x hx
    rw [evalHOLFinite_eq_toExact] at hx
    split
    · rename_i nz
      split
      · exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have st := hb F (decClockHOLFinite s) code dom aw sl ⟨pre,hc s x aw pre sl hx nz⟩
        have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        cases run : evaluateHOLFiniteState (decClockHOLFinite s) body with
        | mk result middle =>
          rw [run] at st meta' remaining
          obtain ⟨m1,a1,n1,r1,c1,b1⟩ := st
          have smaller : middle.clock < s.clock := by
            change middle.clock ≤ s.clock - 1 at remaining
            omega
          cases result with
          | none =>
            obtain ⟨sl1,i1⟩ := n1 rfl
            have again := aqm_while_run c body hc hb middle (meta'.1.trans code) (by rw [meta'.2.1]; exact dom)
              (a1 (Or.inl rfl)) sl1 i1
            exact ⟨again.1.trans m1,again.2⟩
          | some result =>
            cases result with
            | «continue» => exact absurd rfl c1
            | «break» => exact absurd rfl b1
            | returned v => exact ⟨m1,a1,(fun e => by cases e),r1,by simp,by simp⟩
            | exception _ _ => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
            | finalFfi _ => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
            | error => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
            | timeOut => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
    · exact ⟨rfl,fun _ => aw,fun _ => ⟨sl,pre⟩,(fun v e => by cases e),by simp,by simp⟩
  · exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
termination_by s.clock

theorem aqm_while {I C : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} (c : ExpHOL 64) {body : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), AW SP0 P0 FM G0 s.globals →
      I s.locals s.memory → SL Vn s.locals → EV s c = some (.val (.word x)) → x ≠ 0 → C s.locals s.memory)
    (hb : AQM SP0 P0 FM G0 w Vn (fun L M => I L M ∧ C L M) I RR body) : AQM SP0 P0 FM G0 w Vn I I RR (.while c body) :=
  fun F s code dom aw sl pre => aqm_while_run c body hc hb s code dom aw sl pre

theorem aqm_dec {P Pb Qb Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} (name : MlS) (shape : ShapeHOL)
    (init : ExpHOL 64) {body : ProgHOL 64} (hshape : Vn name → shape = .one)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, AW SP0 P0 FM G0 s.globals → P s.locals s.memory →
      SL Vn s.locals → EV s init = some v → shapeEqHOL shape (shapeOfHOLExact v) = true →
      Pb (s.locals.update (name,v)) s.memory)
    (hb : AQM SP0 P0 FM G0 w Vn Pb Qb RR body)
    (hq : ∀ L M L' M', P L M → Qb L' M' → Q (L'.resVarEq (name,L.lookup name)) M') :
    AQM SP0 P0 FM G0 w Vn P Q RR (.dec name shape init body) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · rename_i v hv
    split
    · rename_i hs
      have slb : SL Vn (setVarHOLFinite name v s).locals :=
        sl_update sl name v (fun hn => by rw [hshape hn] at hs; exact scalar_of_shape hs)
      obtain ⟨m1,a1,n1,r1,c1,b1⟩ := hb F (setVarHOLFinite name v s) (by exact code) (by exact dom) (by exact aw) slb
        (hi s v aw pre sl hv hs)
      exact ⟨m1,a1,fun e => ⟨sl_restore (n1 e).1 sl name,hq _ _ _ _ pre (n1 e).2⟩,r1,c1,b1⟩
    · exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aqm_assignLocal {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} (x : MlS) (e : ExpHOL 64)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, AW SP0 P0 FM G0 s.globals → P s.locals s.memory →
      SL Vn s.locals → EV s e = some v → Q (s.locals.update (x,v)) s.memory) :
    AQM SP0 P0 FM G0 w Vn P Q RR (.assign .local x e) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_assign]
  split
  · exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · rename_i v hv
    split
    · rename_i valid
      refine ⟨rfl,fun _ => aw,fun _ => ⟨?_,hi s v aw pre sl hv⟩,(fun v e => by cases e),by simp,by simp⟩
      apply sl_update sl x v
      intro hx
      simp only [isValidValueHOLFinite,lookupKvarHOLFinite] at valid
      split at valid
      · rename_i old hold
        obtain ⟨y,rfl⟩ := sl x hx old hold
        exact scalar_of_shape' (by simpa [shapeOfHOLExact] using valid)
      · cases valid
    · exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

theorem aqm_return {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} (e : ExpHOL 64)
    (hr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, AW SP0 P0 FM G0 s.globals → P s.locals s.memory →
      SL Vn s.locals → EV s e = some v → RR v s.memory) :
    AQM SP0 P0 FM G0 w Vn P Q RR (.return e) := by
  intro F s code dom aw sl pre
  rw [evaluateHOLFiniteState_return]
  split
  · exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  · rename_i v hv
    split
    · refine ⟨rfl,fun _ => aw,(fun e => by cases e),fun v' e => ?_,by simp,by simp⟩
      simp only [Option.some.injEq,PanSemResultExact.returned.injEq] at e
      subst e
      exact hr s v aw pre sl hv
    · exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- A successful word store writes exactly its word. -/
theorem store_none_mem {F : Type} (s : PanSemStateFiniteExact 64 F) (d v : ExpHOL 64) (a y : BitVec 64)
    (hd : EV s d = some (.val (.word a))) (hv : EV s v = some (.val (.word y)))
    (h : (evaluateHOLFiniteState s (.store d v)).1 = none) :
    (evaluateHOLFiniteState s (.store d v)).2.memory = fun x => if x = a then .word y else s.memory x := by
  simp only [EV] at hd hv
  revert h
  rw [evaluateHOLFiniteState_store,hd]
  dsimp only
  rw [hv]
  dsimp only
  simp only [flattenHOL,panMemStoresHOL,panMemStoreHOL]
  split
  · rename_i m hm
    intro _
    split at hm
    · rename_i upd hupd
      simp only [Option.some.injEq] at hm
      subst hm
      split at hupd
      · simp only [Option.some.injEq] at hupd
        rw [← hupd]
      · cases hupd
    · cases hm
  · intro h; cases h

/-- A word store: the normal postcondition sees the stored word. -/
theorem aqm_store {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), AW SP0 P0 FM G0 s.globals → P s.locals s.memory →
      SL Vn s.locals → ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ w ≠ a ∧
        ∀ y : BitVec 64, EV s v = some (.val (.word y)) →
          Q s.locals (fun x => if x = a then .word y else s.memory x))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, AW SP0 P0 FM G0 s.globals → P s.locals s.memory →
      SL Vn s.locals → EV s v = some x → ∃ y : BitVec 64, x = .val (.word y)) :
    AQM SP0 P0 FM G0 w Vn P Q RR (.store d v) := by
  intro F s code dom aw sl pre
  obtain ⟨a,ha,ne,hq⟩ := hd s aw pre sl
  obtain ⟨res,_,loc,glob,mem⟩ := evaluate_store_word_frame s d v a ha (hv s · aw pre sl)
  refine ⟨mem w ne,fun _ => by rw [glob]; exact aw,fun e => ⟨by rw [loc]; exact sl,?_⟩,?_,?_,?_⟩
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
      obtain ⟨y,rfl⟩ := hv s x aw pre sl hvv
      rw [loc,store_none_mem s d v a y ha hvv e]
      exact hq y hvv
  · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
  all_goals rcases res with h | h <;> rw [h] <;> simp

/-- A byte store: the normal postcondition holds for any memory that differs only at the aligned word. -/
theorem aqm_storeByte {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), AW SP0 P0 FM G0 s.globals → P s.locals s.memory →
      SL Vn s.locals → ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ w ≠ panByteAlignHOL a ∧
        ∀ M' : Mem, (∀ x, x ≠ panByteAlignHOL a → M' x = s.memory x) → Q s.locals M') :
    AQM SP0 P0 FM G0 w Vn P Q RR (.storeByte d v) := by
  intro F s code dom aw sl pre
  obtain ⟨a,ha,ne,hq⟩ := hd s aw pre sl
  obtain ⟨res,_,loc,glob,_,_,_⟩ := evaluate_storeByte_control_frame s d v
  refine ⟨evaluate_storeByte_memory_frame s d v a w ha ne,fun _ => by rw [glob]; exact aw,
    fun _ => ⟨by rw [loc]; exact sl,by rw [loc]; exact hq _ (fun x hx => evaluate_storeByte_memory_frame s d v a x ha hx)⟩,
    ?_,?_,?_⟩
  · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
  all_goals rcases res with h | h <;> rw [h] <;> simp

/-- A discarded call against a callee spec: the callee body is memory-aware arena-safe from entry locals/memory
satisfying `Pe` (relative to the caller's locals and memory), and a callee return establishes `Q` through `RRe`. -/
theorem aqm_callSpec {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} {Vn' : MlS → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → ValueHOL 64 → Mem → Prop)
    (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ L0 M0, P L0 M0 → AQM SP0 P0 FM G0 w Vn' (Pe L0 M0) (fun _ _ => True) (RRe L0 M0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, AW SP0 P0 FM G0 s.globals →
      P s.locals s.memory → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory callee s.memory)
    (hq : ∀ L M v M', P L M → RRe L M v M' → Q L M') :
    AQM SP0 P0 FM G0 w Vn P Q RR (.call (some (none,none)) function arguments) := by
  intro F state code dom aw sl pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
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
      · exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (sl_mono esl (fun _ _ => trivial)) (hpe state values callee foundShape aw pre sl args lookup')
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals first
            | exact ⟨m1,fun _ => a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),fun _ => ⟨sl,hq _ _ _ _ pre (r1 _ rfl)⟩,
                (fun v e => by cases e),by simp,by simp⟩
            | exact aqm_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- A declared call against a callee spec. -/
theorem aqm_decCallSpec {P Pc Qc Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} {Vn' : MlS → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → ValueHOL 64 → Mem → Prop)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ L0 M0, P L0 M0 → AQM SP0 P0 FM G0 w Vn' (Pe L0 M0) (fun _ _ => True) (RRe L0 M0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, AW SP0 P0 FM G0 s.globals →
      P s.locals s.memory → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory callee s.memory)
    (hshape : Vn name → shape = .one)
    (hret : ∀ L M v M', P L M → RRe L M v M' → shapeEqHOL (shapeOfHOLExact v) shape = true →
      Pc (L.update (name,v)) M')
    (hc : AQM SP0 P0 FM G0 w Vn Pc Qc RR cont)
    (hq : ∀ L M L' M', P L M → Qc L' M' → Q (L'.resVarEq (name,L.lookup name)) M') :
    AQM SP0 P0 FM G0 w Vn P Q RR (.decCall name shape function arguments cont) := by
  intro F state code dom aw sl pre
  rw [evaluateHOLFiniteState_decCall_total]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
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
      · exact aqm_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (sl_mono esl (fun _ _ => trivial)) (hpe state values callee foundShape aw pre sl args lookup')
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame meta'
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          dsimp only [fixClockHOLFinite]
          cases rb with
          | none => exact aqm_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · rename_i ok
                simp only [Bool.and_eq_true] at ok
                have cslx : SL Vn (state.locals.update (name,v)) :=
                  sl_update sl name v (fun hn => by rw [hshape hn] at ok; exact scalar_of_shape' ok.1)
                have pc := hret _ _ _ _ pre (r1 v rfl) ok.1
                obtain ⟨m2,a2,n2,r2,c2,b2⟩ := hc F (setVarHOLFinite name v { bodyPost with clock := _, locals := state.locals })
                  (by exact meta'.1.trans code) (by intro a ha; exact dom a (meta'.2.1 ▸ ha))
                  (by exact a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))) cslx pc
                exact ⟨m2.trans m1,a2,fun e => ⟨sl_restore (n2 e).1 sl name,hq _ _ _ _ pre (n2 e).2⟩,r2,c2,b2⟩
              · exact aqm_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
            | _ => exact aqm_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

#print axioms aqm_seq
#print axioms aqm_while
#print axioms aqm_dec
#print axioms aqm_store
#print axioms aqm_storeByte
#print axioms aqm_callSpec
#print axioms aqm_decCallSpec
end InitECandidate.Runtime
