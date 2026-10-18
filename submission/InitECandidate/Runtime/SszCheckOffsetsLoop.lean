import InitECandidate.Runtime.SszCheckOffsetsStep
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Loop states differ from a base state only in locals and clock; every
offset below i has been accepted. -/
def SszCheckInv {σ : Type} (base : PanSemStateFiniteExact 64 σ) (offs n fixed len : BitVec 64)
    (s : PanSemStateFiniteExact 64 σ) : Prop :=
  ∃ i : BitVec 64, ∃ L, s = {base with locals := L, clock := s.clock} ∧
    L.lookup (ofString "offs") = some (.val (.word offs)) ∧ L.lookup (ofString "n") = some (.val (.word n)) ∧
    L.lookup (ofString "fixed") = some (.val (.word fixed)) ∧ L.lookup (ofString "len") = some (.val (.word len)) ∧
    L.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ n.toNat ∧ n.toNat < 2 ^ 63 ∧
    ∀ k : BitVec 64, k.toNat < i.toNat → SszOffsetOK base offs fixed len k

def sszCheckRank {σ : Type} (s : PanSemStateFiniteExact 64 σ) : Nat :=
  match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "n") with
  | some (.val (.word i)), some (.val (.word n)) => n.toNat - i.toNat
  | _, _ => 0

theorem sszCheck_rank_eq {σ : Type} (s : PanSemStateFiniteExact 64 σ) (i n : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n))) :
    sszCheckRank s = n.toNat - i.toNat := by
  simp [sszCheckRank, hi, hn]

theorem evaluate_sszCheckLoop {σ : Type} (base : PanSemStateFiniteExact 64 σ) (offs n fixed len : BitVec 64)
    (code : base.code = originalRuntimeCode)
    (s : PanSemStateFiniteExact 64 σ) (inv : SszCheckInv base offs n fixed len s)
    (ticks : sszCheckRank s * 2 ≤ s.clock) :
    ∃ result post, evaluateHOLFiniteState s sszCheckLoop = (result, post) ∧
      s.clock ≤ post.clock + sszCheckRank s * 2 ∧ post.clock ≤ s.clock ∧ result ≠ some .timeOut ∧
      (result = none → SszCheckInv base offs n fixed len post ∧ sszCheckRank post = 0) ∧
      (∀ value, result ≠ some (.returned value)) := by
  have guard : ∀ state, SszCheckInv base offs n fixed len state →
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if sszCheckRank state = 0 then 0 else 1))) := by
    rintro state ⟨i, L, shape, ho, hn, hf, hl, hi, le, small, _⟩
    have si : state.locals.lookup (ofString "i") = some (.val (.word i)) := by rw [shape]; exact hi
    have sn : state.locals.lookup (ofString "n") = some (.val (.word n)) := by rw [shape]; exact hn
    rw [sszCheck_rank_eq state i n si sn]
    by_cases zero : n.toNat - i.toNat = 0
    · simp [evalHOLFinite, evalHOLExact, si, sn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, zero]
      rw [if_pos (by omega)]; omega
    · simp [evalHOLFinite, evalHOLExact, si, sn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, zero]
      rw [if_pos (by omega)]; omega
  have entry : ∀ state, SszCheckInv base offs n fixed len state →
      SszCheckInv base offs n fixed len (decClockHOLFinite state) := by
    rintro state ⟨i, L, shape, rest⟩
    exact ⟨i, L, by rw [shape]; rfl, rest⟩
  have entryRank : ∀ state : PanSemStateFiniteExact 64 σ, sszCheckRank (decClockHOLFinite state) = sszCheckRank state := by
    intro state; rfl
  have step : ∀ state, SszCheckInv base offs n fixed len state → 0 < sszCheckRank state → 1 ≤ state.clock →
      ∃ post, state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧
        ((evaluateHOLFiniteState state sszCheckStep = (none,post) ∧ SszCheckInv base offs n fixed len post ∧
            sszCheckRank post < sszCheckRank state) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ value, result ≠ .returned value) ∧
           evaluateHOLFiniteState state sszCheckStep = (some result,post))) := by
    rintro state ⟨i, L, shape, ho, hn, hf, hl, hi, le, small, accepted⟩ positive clock
    have look : ∀ k, state.locals.lookup k = L.lookup k := by intro k; rw [shape]
    have si := (look _).trans hi
    have sn := (look _).trans hn
    rw [sszCheck_rank_eq state i n si sn] at positive
    have stateCode : state.code = originalRuntimeCode := by rw [shape]; exact code
    obtain ⟨c1, c2, outcome⟩ := sszCheckStep_outcome state offs n fixed len i ((look _).trans ho) sn
      ((look _).trans hf) ((look _).trans hl) si stateCode (by omega)
    cases run : evaluateHOLFiniteState state sszCheckStep with
    | mk result post =>
      rw [run] at c1 c2 outcome
      dsimp only at c1 c2 outcome
      refine ⟨post, c1, c2, ?_⟩
      rcases outcome with ⟨none_, ⟨L', postShape, ho', hn', hf', hl', hi'⟩, ok⟩ | ⟨x, hx, ab⟩
      · subst none_
        have succ : (i + 1).toNat = i.toNat + 1 := by
          rw [BitVec.toNat_add]; simp; omega
        refine Or.inl ⟨rfl, ⟨i + 1, L', ?_, ho', hn', hf', hl', hi', by omega, small, ?_⟩, ?_⟩
        · rw [postShape, shape]
        · intro k lt
          rw [succ] at lt
          by_cases eq : k.toNat = i.toNat
          · have : k = i := BitVec.eq_of_toNat_eq eq
            subst this
            have ok' := ok
            rw [shape] at ok'
            exact ok'
          · exact accepted k (by omega)
        · have pi : post.locals.lookup (ofString "i") = some (.val (.word (i + 1))) := by rw [postShape]; exact hi'
          have pn : post.locals.lookup (ofString "n") = some (.val (.word n)) := by rw [postShape]; exact hn'
          rw [sszCheck_rank_eq post (i + 1) n pi pn, sszCheck_rank_eq state i n si sn, succ]
          omega
      · subst hx
        exact Or.inr ⟨x, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2, rfl⟩
  have result := evaluate_ranked_loop_exits_invariant _ sszCheckStep (SszCheckInv base offs n fixed len)
    sszCheckRank 1 guard entry entryRank step s inv (by simpa using ticks)
  simpa [sszCheckLoop] using result

#print axioms evaluate_sszCheckLoop
end InitECandidate.Runtime
