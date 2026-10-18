import InitECandidate.Runtime.DecodeRequestsAllocReturned
import InitECandidate.Runtime.DecodeRequestsLoopFrame
import InitECandidate.Runtime.DiscardCallNoReturn
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem sszOffsetOK_congr {σ : Type} (s t : PanSemStateFiniteExact 64 σ) (offs fixed len k : BitVec 64)
    (hm : s.memory = t.memory) (hd : s.memaddrs = t.memaddrs) (h : SszOffsetOK s offs fixed len k) :
    SszOffsetOK t offs fixed len k := by
  unfold SszOffsetOK at h ⊢; rw [← hm, ← hd]; exact h

theorem sszCheckOffsetsReturned_congr {σ : Type} (s t : PanSemStateFiniteExact 64 σ) (offs n fixed len : BitVec 64)
    (v : ValueHOL 64) (hm : s.memory = t.memory) (hd : s.memaddrs = t.memaddrs)
    (h : SszCheckOffsetsReturned s offs n fixed len v) : SszCheckOffsetsReturned t offs n fixed len v := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨a, fun k hk => sszOffsetOK_congr s t offs fixed len k hm hd (b k hk), by rw [← hm, ← hd]; exact c⟩

theorem reqArrayFacts_congr {σ : Type} (s t : PanSemStateFiniteExact 64 σ) (p L pointer offsets : BitVec 64)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 σ)
    (hm : s.memory = t.memory) (hd : s.memaddrs = t.memaddrs) (hg : s.globals = t.globals)
    (h : ReqArrayFacts s p L pointer offsets v post) : ReqArrayFacts t p L pointer offsets v post := by
  unfold ReqArrayFacts setGlobalHOLFinite at h ⊢
  rw [← hm, ← hd, ← hg]; exact h

/-- Returned contract of the actual decode_requests body: the input is at
least 20 bytes; the scratch cells hold offsets accepted by ssz_check_offsets
(memory otherwise unchanged); the five list lengths divide exactly; rq is the
entry heap pointer with 80 bytes allocated; the ten request cells hold
p+o_k and n_k; globals change only in heap_ptr; and the domain is unchanged. -/
def DecodeRequestsReturned {σ : Type} (e : PanSemStateFiniteExact 64 σ) (p L pointer offsets : BitVec 64)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 σ) : Prop :=
  ¬ L < 20 ∧ ∃ M1 : BitVec 64 → HolWordLab 64,
    (∀ a, (∀ k : BitVec 64, k.toNat < 5 → a ≠ offsets + k * 8) → M1 a = e.memory a) ∧
    SszCheckOffsetsReturned ({e with memory := M1} : PanSemStateFiniteExact 64 σ) offsets 5 20 L (.val (.word 0)) ∧
    ReqArrayFacts ({e with memory := M1} : PanSemStateFiniteExact 64 σ) p L pointer offsets v post

theorem evaluate_decodeRequests_returned_enough {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (p L pointer offsets : BitVec 64) (installed : e.code = originalRuntimeCode)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word L)))
    (heap : e.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (hg : e.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets))) (enough : 354 ≤ e.clock) :
    ∀ v, (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_decode_requests)).1 = some (.returned v) →
      DecodeRequestsReturned e p L pointer offsets v
        (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_decode_requests)).2 := by
  intro v returned
  rw [source_decodeRequests_body, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at returned ⊢
  by_cases short : L < 20
  · have cond : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
        (.cmp .lower (sszLocal "len") (.const 20)) = some (.val (.word 1#64)) := by
      simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact short
    rw [cond] at returned
    dsimp only at returned
    rw [if_neg (by decide : ¬ (1#64 : BitVec 64) = 0)] at returned
    obtain ⟨x, run, abnormal, _, _⟩ := sszFail_abnormal e 60 installed (by omega)
    rw [run] at returned
    dsimp only at returned
    exact absurd (Option.some.inj (run.symm.trans returned)) (abnormal.2.2.2 v)
  · have cond : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
        (.cmp .lower (sszLocal "len") (.const 20)) = some (.val (.word 0#64)) := by
      simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact BitVec.not_lt.mp short
    rw [cond] at returned ⊢
    dsimp only at returned ⊢
    rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip] at returned ⊢
    dsimp only at returned ⊢
    unfold reqAfterLen at returned ⊢
    rw [evaluateHOLFiniteState_dec_total] at returned ⊢
    dsimp only at returned ⊢
    simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at returned ⊢
    generalize hq : setVarHOLFinite (ofString "i") (.val (.word 0#64)) e = q at returned ⊢
    have qi : q.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
      rw [← hq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have qg : q.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by rw [← hq]; exact hg
    have rank : reqLoopRank q = 5 := by simp [reqLoopRank, qi]
    have qc : q.clock = e.clock := by rw [← hq]; rfl
    obtain ⟨result, post1, run1, normal⟩ := evaluate_reqLoop_frame q q offsets qg
      ⟨0#64, q.locals, q.memory, rfl, qi, by simp, fun _ _ => rfl, fun _ _ => rfl⟩ (by omega)
    obtain ⟨result', post1', run1', _, _, _, _, noret⟩ := evaluate_reqLoop q q
      ⟨0#64, q.locals, q.memory, rfl, qi, by simp, fun _ _ => rfl⟩ (by omega)
    rw [run1] at run1'
    obtain ⟨rr, _⟩ := Prod.mk.inj run1'
    subst rr
    rw [evaluateHOLFiniteState_seq_line780, run1] at returned ⊢
    cases result with
    | some x =>
      dsimp only at returned
      exact (noret v returned).elim
    | none =>
      dsimp only at returned ⊢
      obtain ⟨⟨i, L1, M1, shape, hi1, le1, others, frame⟩, zero⟩ := normal rfl
      have pi : post1.locals.lookup (ofString "i") = some (.val (.word i)) := by rw [shape]; exact hi1
      have ieq : i.toNat = 5 := by simp [reqLoopRank, pi] at zero; omega
      have li : ofString "len" ≠ ofString "i" := by decide_cbv
      have pii : ofString "p" ≠ ofString "i" := by decide_cbv
      have p1len : post1.locals.lookup (ofString "len") = some (.val (.word L)) := by
        rw [shape]; dsimp only; rw [others _ li, ← hq]
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm li, hlen]
      have p1p : post1.locals.lookup (ofString "p") = some (.val (.word p)) := by
        rw [shape]; dsimp only; rw [others _ pii, ← hq]
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm pii, hp]
      have p1g : post1.globals = e.globals := by rw [shape, ← hq]; rfl
      have p1d : post1.memaddrs = e.memaddrs := by rw [shape, ← hq]; rfl
      have p1m : post1.memory = M1 := by rw [shape]
      have p1c : post1.code = originalRuntimeCode := by rw [shape, ← hq]; exact installed
      rw [evaluateHOLFiniteState_seq_line780] at returned ⊢
      cases run2 : evaluateHOLFiniteState post1 reqCheck with
      | mk r2 post2 =>
        rw [run2] at returned
        cases r2 with
        | some x =>
          dsimp only at returned
          have nr := evaluate_discard_call_no_return post1 (ofString "ssz_check_offsets")
            [reqGlobal, .const 5, .const 20, sszLocal "len"] v
          unfold reqCheck at run2
          rw [run2] at nr
          exact absurd returned nr
        | none =>
          dsimp only at returned ⊢
          obtain ⟨checked, l2, m2, g2, d2, c2⟩ := reqCheck_normal post1 post2 offsets L (by rw [p1g]; exact hg) p1len
            p1c run2
          cases run3 : evaluateHOLFiniteState post2 reqAlloc with
          | mk r3 post3 =>
            rw [run3] at returned
            dsimp only at returned ⊢
            subst returned
            have facts := reqAlloc_returned post2 post3 p L pointer offsets v (c2.trans p1c)
              (by rw [l2]; exact p1p) (by rw [l2]; exact p1len) (by rw [g2, p1g]; exact heap) pointerBound
              (by rw [g2, p1g]; exact hg) run3
            refine ⟨short, M1, fun a ex => ?_, ?_, ?_⟩
            · rw [frame a (fun k hk => ex k (by omega)), ← hq]; rfl
            · exact sszCheckOffsetsReturned_congr _ _ offsets 5 20 L _ (by rw [← p1m]; rfl) (by rw [← p1d]; rfl) checked
            · exact reqArrayFacts_congr post2 _ p L pointer offsets v post3 (by rw [m2, p1m]) (by rw [d2, p1d])
                (by rw [g2, p1g]) facts

#print axioms evaluate_decodeRequests_returned_enough

/-- At any clock, every return of the actual decode_requests body satisfies the contract. -/
theorem evaluate_decodeRequests_returned {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (p L pointer offsets : BitVec 64) (installed : e.code = originalRuntimeCode)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word L)))
    (heap : e.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (hg : e.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets))) :
    ∀ v, (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_decode_requests)).1 = some (.returned v) →
      DecodeRequestsReturned e p L pointer offsets v
        (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_decode_requests)).2 := by
  intro v returned
  let out := evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_decode_requests)
  let lifted : PanSemStateFiniteExact 64 σ := {e with clock := e.clock + 354}
  have run : evaluateHOLFiniteState lifted (sourceFunctionBody Guest.guestFn_decode_requests) =
      (out.1, {out.2 with clock := out.2.clock + 354}) :=
    panPropsEvaluateAddClockEq _ e out.1 out.2 _ ⟨rfl, by change out.1 ≠ _; rw [returned]; simp⟩
  have high := evaluate_decodeRequests_returned_enough lifted p L pointer offsets installed hp hlen heap pointerBound hg
    (by simp [lifted]) v (by rw [run]; exact returned)
  rw [run] at high
  obtain ⟨short, M1, frame, checked, facts⟩ := high
  exact ⟨short, M1, frame, sszCheckOffsetsReturned_congr _ _ offsets 5 20 L _ rfl rfl checked,
    reqArrayFacts_congr _ _ p L pointer offsets v _ rfl rfl rfl facts⟩

#print axioms evaluate_decodeRequests_returned
end InitECandidate.Runtime
