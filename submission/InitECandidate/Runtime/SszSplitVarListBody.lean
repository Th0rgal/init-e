import InitECandidate.Runtime.SszSplitVarListFirstStage
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returned contract of the actual ssz_split_var_list: either the empty list,
or an accepted first offset, count = first/4 within lim, an allocation of
count*16 bytes at the entry heap pointer, and the returned <arr,count>. -/
def SszSplitVarListReturned {σ : Type} (e : PanSemStateFiniteExact 64 σ) (len lim pointer : BitVec 64)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 σ) : Prop :=
  (len = 0 ∧ v = .rStruct [.val (.word 0), .val (.word 0)] ∧ post.globals = e.globals) ∨
  (¬ len < 4 ∧ ∃ first, @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
      sszSplitFirst = some (.val (.word first)) ∧ SszSplitFirstOK len first ∧
    SszSplitAllocReturned e lim (first >>> (2 : Nat)) pointer v post)

def sszSplitBound (len : BitVec 64) : Nat := 2 * (len.toNat / 4) + 2

theorem evaluate_sszSplitVarList_body_enough {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (p len lim pointer : BitVec 64) (installed : e.code = originalRuntimeCode)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word len)))
    (hlim : e.locals.lookup (ofString "lim") = some (.val (.word lim)))
    (heap : e.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (enough : sszSplitBound len ≤ e.clock) :
    let out := evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
    e.clock ≤ out.2.clock + sszSplitBound len ∧ out.2.clock ≤ e.clock ∧ out.1 ≠ none ∧ out.1 ≠ some .timeOut ∧
      (∀ v, out.1 = some (.returned v) → SszSplitVarListReturned e len lim pointer v out.2) := by
  unfold sszSplitBound at enough ⊢
  have f1 : ofString "first" ≠ ofString "p" := by decide_cbv
  have f2 : ofString "first" ≠ ofString "len" := by decide_cbv
  have f3 : ofString "first" ≠ ofString "lim" := by decide_cbv
  rw [source_sszSplitVarList_body, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  by_cases zero : len = 0
  · subst zero
    have cond : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
        (.cmp .equal (sszLocal "len") (.const 0)) = some (.val (.word 1#64)) := by
      simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [cond]
    simp [evalHOLExact, evalListHOLExact, shapeOfHOLExact, emptyLocalsHOLFinite, SszSplitVarListReturned]
  · have cond : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
        (.cmp .equal (sszLocal "len") (.const 0)) = some (.val (.word 0#64)) := by
      simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      exact zero
    rw [cond]
    dsimp only
    rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    by_cases short : len < 4
    · have cond4 : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
          (.cmp .lower (sszLocal "len") (.const 4)) = some (.val (.word 1#64)) := by
        simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact short
      rw [cond4]
      dsimp only
      rw [if_neg (by decide : ¬ (1#64 : BitVec 64) = 0)]
      obtain ⟨x, run, abnormal, c1, c2⟩ := sszFail_abnormal e 20 installed (by omega)
      rw [run]
      dsimp only
      exact ⟨by omega, c2, by rw [run]; simp, fun h => abnormal.2.1 (Option.some.inj (run.symm.trans h)),
        fun v h => absurd (Option.some.inj (run.symm.trans h)) (abnormal.2.2.2 v)⟩
    · have cond4 : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
          (.cmp .lower (sszLocal "len") (.const 4)) = some (.val (.word 0#64)) := by
        simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact BitVec.not_lt.mp short
      rw [cond4]
      dsimp only
      rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip]
      dsimp only
      cases init : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a)) sszSplitFirst with
      | none =>
        rw [evaluateHOLFiniteState_dec_total]
        dsimp only
        simp only [init]
        exact ⟨by omega, Nat.le_refl _, by simp, by simp, fun v h => by simp at h⟩
      | some value =>
        cases value
        case val wl =>
          cases wl with
          | word first =>
            apply evaluate_dec_word_post e (ofString "first") _ _ first _
              (fun r t => r ≠ none ∧ r ≠ some .timeOut ∧ ∀ v, r = some (.returned v) →
                SszSplitVarListReturned e len lim pointer v t)
              (fun _ _ _ h => h) init
            generalize hd : setVarHOLFinite (ofString "first") (.val (.word first)) e = d
            have up : ∀ k, k ≠ ofString "first" → d.locals.lookup k = e.locals.lookup k := by
              intro k hk; rw [← hd]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
            have dc : d.clock = e.clock := by rw [← hd]; rfl
            obtain ⟨s1, s2, s3, s4, s5⟩ := evaluate_sszSplitFirstStage d p len first lim pointer
              ((up _ f1.symm).trans hp) ((up _ f2.symm).trans hlen)
              (by rw [← hd]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
              ((up _ f3.symm).trans hlim) (by rw [← hd]; exact installed) (by rw [← hd]; exact heap) pointerBound
              (by omega)
            refine ⟨by omega, by omega, s3, s4, fun v h => Or.inr ⟨short, first, init, ?_⟩⟩
            obtain ⟨ok, x1, x2, x3, x4⟩ := s5 v h
            exact ⟨ok, x1, x2, x3, x4.trans (by rw [← hd]; rfl)⟩
        all_goals
          rw [evaluateHOLFiniteState_dec_total]
          dsimp only
          simp only [init]
          simp [shapeOfHOLExact, shapeEqHOL]

#print axioms evaluate_sszSplitVarList_body_enough

/-- The actual ssz_split_var_list body at any clock: at most 2*(len/4)+2
clocks, no timeout with that much clock, never none, and every return
satisfies the slice-array/allocation contract. -/
theorem evaluate_sszSplitVarList_body {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (p len lim pointer : BitVec 64) (installed : e.code = originalRuntimeCode)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word len)))
    (hlim : e.locals.lookup (ofString "lim") = some (.val (.word lim)))
    (heap : e.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) :
    let out := evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
    e.clock ≤ out.2.clock + sszSplitBound len ∧ out.2.clock ≤ e.clock ∧
      (sszSplitBound len ≤ e.clock → out.1 ≠ some .timeOut) ∧ out.1 ≠ none ∧
      (∀ v, out.1 = some (.returned v) → SszSplitVarListReturned e len lim pointer v out.2) := by
  by_cases enough : sszSplitBound len ≤ e.clock
  · obtain ⟨a, b, c, d, f⟩ := evaluate_sszSplitVarList_body_enough e p len lim pointer installed hp hlen hlim heap
      pointerBound enough
    exact ⟨a, b, fun _ => d, c, f⟩
  · intro out
    have lower := evaluateHOLFiniteState_clock_le e (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
    let lifted : PanSemStateFiniteExact 64 σ := {e with clock := e.clock + sszSplitBound len}
    have high := evaluate_sszSplitVarList_body_enough lifted p len lim pointer installed hp hlen hlim heap
      pointerBound (by simp [lifted])
    have same : out.1 ≠ some .timeOut →
        evaluateHOLFiniteState lifted (sourceFunctionBody Guest.guestFn_ssz_split_var_list) =
          (out.1, {out.2 with clock := out.2.clock + sszSplitBound len}) :=
      fun nt => panPropsEvaluateAddClockEq _ e out.1 out.2 _ ⟨rfl, nt⟩
    have he : @evalHOLExact 64 σ _ lifted.toExact (fun a => Classical.propDecidable (lifted.memaddrs a)) sszSplitFirst =
        @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a)) sszSplitFirst :=
      @evalHOLExact_upd_clock_eq 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a)) sszSplitFirst _
    refine ⟨by omega, lower, fun h => absurd h enough, ?_, ?_⟩
    · intro none_
      have run := same (by rw [none_]; simp)
      exact high.2.2.1 (by rw [run]; exact none_)
    · intro v returned
      have run := same (by rw [returned]; simp)
      have contract := high.2.2.2.2 v (by rw [run]; exact returned)
      rw [run] at contract
      rcases contract with ⟨a, b, c⟩ | ⟨a, first, hf, ok, ar⟩
      · exact Or.inl ⟨a, b, c⟩
      · exact Or.inr ⟨a, first, he.symm.trans hf, ok, ar⟩

#print axioms evaluate_sszSplitVarList_body
end InitECandidate.Runtime
