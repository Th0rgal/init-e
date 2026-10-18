import InitECandidate.Runtime.StatelessWitnessSetupRun
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Two runs agree in result, clock, memory, globals and domain (locals may differ by scope restoration). -/
def Scoped {σ : Type} (a b : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  a.1 = b.1 ∧ a.2.clock = b.2.clock ∧ a.2.memory = b.2.memory ∧ a.2.globals = b.2.globals ∧ a.2.memaddrs = b.2.memaddrs

theorem scoped_refl {σ : Type} (a : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Scoped a a :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem scoped_trans {σ : Type} {a b c : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    (h1 : Scoped a b) (h2 : Scoped b c) : Scoped a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.1.trans h2.2.2.2.1,
    h1.2.2.2.2.trans h2.2.2.2.2⟩

theorem scoped_restore {σ : Type} (o : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) :
    Scoped (o.1, ({o.2 with locals := L} : PanSemStateFiniteExact 64 σ)) o := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Either the program reaches the continuation from a state satisfying P after at most K ticks
(scoped-equal outcome), or it aborts without returning within K ticks. -/
def Reaches {σ : Type} (s : PanSemStateFiniteExact 64 σ) (prog : ProgHOL 64) (P : PanSemStateFiniteExact 64 σ → Prop)
    (K : Nat) (cont : ProgHOL 64) : Prop :=
  (∃ E, P E ∧ s.clock ≤ E.clock + K ∧ E.clock ≤ s.clock ∧
    Scoped (evaluateHOLFiniteState s prog) (evaluateHOLFiniteState E cont)) ∨
  StAbort s (evaluateHOLFiniteState s prog) K

theorem stAbort_scoped {σ : Type} (s : PanSemStateFiniteExact 64 σ) (a b) (K : Nat)
    (sc : Scoped a b) (h : StAbort s b K) : StAbort s a K := by
  obtain ⟨x, h1, h2, h3, h4, h5⟩ := h
  exact ⟨x, sc.1.trans h1, h2, by rw [sc.2.1]; exact h3, by rw [sc.2.1]; exact h4, h5⟩

theorem reaches_trans {σ : Type} (s : PanSemStateFiniteExact 64 σ) (prog cont1 cont2 : ProgHOL 64)
    (P Q : PanSemStateFiniteExact 64 σ → Prop) (K1 K2 : Nat)
    (h1 : Reaches s prog P K1 cont1) (h2 : ∀ E, P E → Reaches E cont1 Q K2 cont2) :
    Reaches s prog Q (K1 + K2) cont2 := by
  rcases h1 with ⟨E, pE, c1, c2, sc⟩ | ab
  · rcases h2 E pE with ⟨F, qF, d1, d2, sc2⟩ | ab2
    · exact Or.inl ⟨F, qF, by omega, by omega, scoped_trans sc sc2⟩
    · right
      obtain ⟨x, h1, h2, h3, h4, h5⟩ := ab2
      have ck := sc.2.1
      exact ⟨x, sc.1.trans h1, h2, by omega, by omega, fun k => h5 (by omega)⟩
  · exact Or.inr (stAbort_mono s _ K1 (K1 + K2) (by omega) ab)

theorem reaches_mono {σ : Type} (s : PanSemStateFiniteExact 64 σ) (prog cont : ProgHOL 64)
    (P Q : PanSemStateFiniteExact 64 σ → Prop) (K K' : Nat) (le : K ≤ K') (pq : ∀ E, P E → Q E)
    (h : Reaches s prog P K cont) : Reaches s prog Q K' cont := by
  rcases h with ⟨E, pE, c1, c2, sc⟩ | ab
  · exact Or.inl ⟨E, pq E pE, by omega, c2, sc⟩
  · exact Or.inr (stAbort_mono s _ K K' le ab)

/-- seq whose first part completes normally at t, or aborts. -/
theorem reaches_seq {σ : Type} (s : PanSemStateFiniteExact 64 σ) (first rest : ProgHOL 64) (K : Nat)
    (P : PanSemStateFiniteExact 64 σ → Prop)
    (h : (∃ t, P t ∧ s.clock ≤ t.clock + K ∧ t.clock ≤ s.clock ∧ evaluateHOLFiniteState s first = (none, t)) ∨
      StAbort s (evaluateHOLFiniteState s first) K) :
    Reaches s (.seq first rest) P K rest := by
  rcases h with ⟨t, pt, c1, c2, run⟩ | ab
  · exact Or.inl ⟨t, pt, c1, c2, by rw [evaluateHOLFiniteState_seq_line780, run]; exact scoped_refl _⟩
  · exact Or.inr (stAbort_seq s first rest K ab)

/-- A word declaration whose initializer evaluates to a word, or fails to evaluate. -/
theorem reaches_dec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (name : MlS) (e : ExpHOL 64) (body : ProgHOL 64)
    (P : PanSemStateFiniteExact 64 σ → Prop)
    (h : ∀ v, @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w) ∧ P (setVarHOLFinite name (.val (.word w)) s)) :
    Reaches s (.dec name .one e body) P 0 body := by
  rw [Reaches, evaluateHOLFiniteState_dec_total]
  dsimp only
  cases he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with
  | none => exact Or.inr (stAbort_error s 0)
  | some v =>
    obtain ⟨w, rfl, pw⟩ := h _ he
    simp only [shapeOfHOLExact, shapeEqHOL, if_true]
    exact Or.inl ⟨_, pw, by simp [setVarHOLFinite], by simp [setVarHOLFinite], scoped_restore _ _⟩

#print axioms reaches_trans
end InitECandidate.Runtime
