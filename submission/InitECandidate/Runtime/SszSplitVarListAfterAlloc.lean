import InitECandidate.Runtime.SszSplitVarListLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Final length store and return of the slice array. -/
theorem evaluate_sszSplitTail {σ : Type} (t : PanSemStateFiniteExact 64 σ) (p len first count arr i prev : BitVec 64)
    (look : SszSplitLocals t.locals p len first count arr i prev) :
    let out := evaluateHOLFiniteState t sszSplitTail
    out.2.clock = t.clock ∧ out.1 ≠ none ∧ out.1 ≠ some .timeOut ∧ out.2.globals = t.globals ∧
      (∀ v, out.1 = some (.returned v) → v = .rStruct [.val (.word arr), .val (.word count)]) := by
  obtain ⟨hp, hlen, hfirst, hcount, harr, hi, hprev⟩ := look
  unfold sszSplitTail
  rw [evaluateHOLFiniteState_seq_line780]
  by_cases dom : t.memaddrs (arr + (count - 1) * 16 + 8)
  · rw [sszStore_in t _ _ _ _ (sszSplit_tailAddr t arr count harr hcount) (sszSplit_diff t len prev "len" "prev" hlen hprev) dom]
    simp [sszLocal, evalHOLExact, evalListHOLExact, harr, hcount, shapeOfHOLExact, emptyLocalsHOLFinite]
  · rw [sszStore_out t _ _ _ _ (sszSplit_tailAddr t arr count harr hcount) (sszSplit_diff t len prev "len" "prev" hlen hprev) dom]
    simp

#print axioms evaluate_sszSplitTail

/-- A word declaration passes clock, result and returned-globals facts of its body. -/
theorem evaluate_dec_word_transfer {σ : Type} (s : PanSemStateFiniteExact 64 σ) (name : MlS) (e : ExpHOL 64)
    (body : ProgHOL 64) (w : BitVec 64) (K : Nat) (Q : Option (PanSemResultExact 64) → Prop)
    (he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some (.val (.word w)))
    (h : s.clock ≤ (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body).2.clock + K ∧
      (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body).2.clock ≤ s.clock ∧
      Q (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body).1 ∧
      (∀ v, (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body).1 = some (.returned v) →
        (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body).2.globals = s.globals)) :
    s.clock ≤ (evaluateHOLFiniteState s (.dec name .one e body)).2.clock + K ∧
      (evaluateHOLFiniteState s (.dec name .one e body)).2.clock ≤ s.clock ∧
      Q (evaluateHOLFiniteState s (.dec name .one e body)).1 ∧
      (∀ v, (evaluateHOLFiniteState s (.dec name .one e body)).1 = some (.returned v) →
        (evaluateHOLFiniteState s (.dec name .one e body)).2.globals = s.globals) := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  simp only [he, shapeOfHOLExact, shapeEqHOL, if_true]
  exact h

/-- SSZ split result facts after the allocation: terminal, timeout-free with
2*count clock, and a return is the array/count pair with globals unchanged. -/
def SszSplitAfterQ (arr count : BitVec 64) (r : Option (PanSemResultExact 64)) : Prop :=
  r ≠ none ∧ r ≠ some .timeOut ∧ ∀ v, r = some (.returned v) → v = .rStruct [.val (.word arr), .val (.word count)]

theorem evaluate_sszSplitInner {σ : Type} (q : PanSemStateFiniteExact 64 σ) (p len first count arr : BitVec 64)
    (look : SszSplitLocals q.locals p len first count arr 0 first)
    (code : q.code = originalRuntimeCode) (small : count.toNat < 2 ^ 62) (enough : 2 * count.toNat ≤ q.clock) :
    q.clock ≤ (evaluateHOLFiniteState q (.seq sszSplitLoop sszSplitTail)).2.clock + 2 * count.toNat ∧
      (evaluateHOLFiniteState q (.seq sszSplitLoop sszSplitTail)).2.clock ≤ q.clock ∧
      SszSplitAfterQ arr count (evaluateHOLFiniteState q (.seq sszSplitLoop sszSplitTail)).1 ∧
      (∀ v, (evaluateHOLFiniteState q (.seq sszSplitLoop sszSplitTail)).1 = some (.returned v) →
        (evaluateHOLFiniteState q (.seq sszSplitLoop sszSplitTail)).2.globals = q.globals) := by
  have inv : SszSplitInv q p len first count arr q := ⟨0#64, first, q.locals, q.memory, rfl, look, by simp, small⟩
  have rank : sszSplitRank q = count.toNat := by
    rw [sszSplit_rank_eq q 0#64 count look.2.2.2.2.2.1 look.2.2.2.1]; simp
  obtain ⟨result, post, run, l1, l2, nt, normal, noret⟩ :=
    evaluate_sszSplitLoop q p len first count arr code q inv (by omega)
  rw [rank] at l1
  rw [evaluateHOLFiniteState_seq_line780, run]
  cases result with
  | none =>
    obtain ⟨⟨i, prev, L, M, shape, look2, _, _⟩, _⟩ := normal rfl
    have postLocals : post.locals = L := by rw [shape]
    have tail := evaluate_sszSplitTail post p len first count arr i prev (by rw [postLocals]; exact look2)
    dsimp only at tail ⊢
    obtain ⟨t1, t2, t3, t4, t5⟩ := tail
    have pg : post.globals = q.globals := by rw [shape]
    exact ⟨by omega, by omega, ⟨t2, t3, t5⟩, fun _ _ => t4.trans pg⟩
  | some x =>
    dsimp only
    exact ⟨by omega, by omega, ⟨by simp, nt, fun v h => absurd h (noret v)⟩, fun v h => absurd h (noret v)⟩

#print axioms evaluate_sszSplitInner
end InitECandidate.Runtime
