import InitECandidate.Runtime.SszCheckOffsetsFinal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Loop then final check from i = 0 with enough clock: terminal, at most
2n+1 clocks, and a return certifies every offset and offs[0] = fixed. -/
theorem evaluate_sszCheckInner {σ : Type} (q : PanSemStateFiniteExact 64 σ) (offs n fixed len : BitVec 64)
    (code : q.code = originalRuntimeCode)
    (hoffs : q.locals.lookup (ofString "offs") = some (.val (.word offs)))
    (hn : q.locals.lookup (ofString "n") = some (.val (.word n)))
    (hfixed : q.locals.lookup (ofString "fixed") = some (.val (.word fixed)))
    (hlen : q.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : q.locals.lookup (ofString "i") = some (.val (.word 0#64)))
    (small : n.toNat < 2 ^ 63) (enough : 2 * n.toNat + 1 ≤ q.clock) :
    let out := evaluateHOLFiniteState q (.seq sszCheckLoop sszCheckFinal)
    q.clock ≤ out.2.clock + (2 * n.toNat + 1) ∧ out.2.clock ≤ q.clock ∧ out.1 ≠ none ∧ out.1 ≠ some .timeOut ∧
      (∀ v, out.1 = some (.returned v) → v = .val (.word 0) ∧
        (∀ k : BitVec 64, k.toNat < n.toNat → SszOffsetOK q offs fixed len k) ∧
        q.memaddrs offs ∧ memWord q.memory offs = fixed) := by
  have inv : SszCheckInv q offs n fixed len q :=
    ⟨0#64, q.locals, rfl, hoffs, hn, hfixed, hlen, hi, by simp, small, fun k lt => by simp at lt⟩
  have rank : sszCheckRank q = n.toNat := by rw [sszCheck_rank_eq q 0#64 n hi hn]; simp
  obtain ⟨result, post, run, l1, l2, nt, normal, noret⟩ :=
    evaluate_sszCheckLoop q offs n fixed len code q inv (by omega)
  rw [rank] at l1
  rw [evaluateHOLFiniteState_seq_line780, run]
  cases result with
  | none =>
    obtain ⟨⟨i, L, shape, ho, hn', hf, hl, hi', le, _, accepted⟩, zero⟩ := normal rfl
    have look : ∀ k, post.locals.lookup k = L.lookup k := by intro k; rw [shape]
    have pi := (look _).trans hi'
    have pn := (look _).trans hn'
    rw [sszCheck_rank_eq post i n pi pn] at zero
    have postCode : post.code = originalRuntimeCode := by rw [shape]; exact code
    have final := evaluate_sszCheckFinal post offs fixed postCode ((look _).trans ho) ((look _).trans hf) (by omega)
    dsimp only at final ⊢
    obtain ⟨f1, f2, f3, f4, f5⟩ := final
    refine ⟨by omega, by omega, f3, f4, fun v h => ?_⟩
    obtain ⟨rfl, dom, eq⟩ := f5 v h
    refine ⟨rfl, fun k lt => accepted k (by omega), ?_, ?_⟩
    · rw [shape] at dom; exact dom
    · rw [shape] at eq; exact eq
  | some x =>
    dsimp only
    exact ⟨by omega, by omega, by simp, nt, fun v h => absurd h (noret v)⟩

#print axioms evaluate_sszCheckInner
end InitECandidate.Runtime
