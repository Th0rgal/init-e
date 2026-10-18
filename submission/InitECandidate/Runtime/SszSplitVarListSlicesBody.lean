import InitECandidate.Runtime.SszSplitVarListSlicesStages
import InitECandidate.Runtime.SszSplitVarListBody
import InitECandidate.Runtime.SszLe32Bound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem sszSplitFirst_count (len first : BitVec 64) (ok : SszSplitFirstOK len first) (small : first.toNat < 2 ^ 32) :
    first >>> (2 : Nat) ≠ 0 ∧ (first >>> (2 : Nat)).toNat < 2 ^ 60 := by
  have cnt : (first >>> (2 : Nat)).toNat = first.toNat / 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have m4 : first.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat ok.2.1
    rw [BitVec.toNat_and] at h
    have e : first.toNat &&& (3 : BitVec 64).toNat = first.toNat % 2 ^ 2 := Nat.and_two_pow_sub_one_eq_mod _ 2
    simp at h e
    omega
  have pos : first.toNat ≠ 0 := fun z => ok.1 (BitVec.eq_of_toNat_eq (by simp [z]))
  refine ⟨fun z => ?_, by omega⟩
  have := congrArg BitVec.toNat z
  rw [cnt] at this
  simp at this
  omega

theorem evaluate_sszSplitFirstStageB {σ : Type} (d : PanSemStateFiniteExact 64 σ)
    (p len first lim pointer : BitVec 64)
    (hp : d.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : d.locals.lookup (ofString "len") = some (.val (.word len)))
    (hfirst : d.locals.lookup (ofString "first") = some (.val (.word first)))
    (hlim : d.locals.lookup (ofString "lim") = some (.val (.word lim)))
    (code : d.code = originalRuntimeCode)
    (heap : d.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (firstSmall : first.toNat < 2 ^ 32)
    (enough : 2 * (len.toNat / 4) + 2 ≤ d.clock) :
    ∀ v, (evaluateHOLFiniteState d sszSplitAfterFirst).1 = some (.returned v) →
      SszSplitSlices d.memory d.memaddrs p len first pointer (first >>> (2 : Nat))
        (evaluateHOLFiniteState d sszSplitAfterFirst).2.memory := by
  have c1n : ofString "count" ≠ ofString "p" := by decide_cbv
  have c2n : ofString "count" ≠ ofString "len" := by decide_cbv
  have c3n : ofString "count" ≠ ofString "first" := by decide_cbv
  have c4n : ofString "count" ≠ ofString "lim" := by decide_cbv
  unfold sszSplitAfterFirst
  rw [evaluateHOLFiniteState_seq_line780]
  by_cases bad : first = 0 ∨ first &&& 3 ≠ 0 ∨ len < first
  · intro v returned
    rw [sszSplitFirstCheck_fail d len first hlen hfirst bad] at returned
    obtain ⟨x, run, abnormal, _, _⟩ := sszFail_abnormal d 21 code (by omega)
    dsimp only at returned
    rw [run] at returned
    dsimp only at returned
    exact absurd (Option.some.inj (run.symm.trans returned)) (abnormal.2.2.2 v)
  · have ok : SszSplitFirstOK len first :=
      ⟨fun h => bad (Or.inl h), Classical.byContradiction fun h' => bad (Or.inr (Or.inl h')),
        fun h => bad (Or.inr (Or.inr h))⟩
    rw [sszSplitFirstCheck_pass d len first hlen hfirst ok]
    dsimp only
    have he : @evalHOLExact 64 σ _ d.toExact (fun a => Classical.propDecidable (d.memaddrs a))
        (.shift .lsr (sszLocal "first") (.const 2)) = some (.val (.word (first >>> (2 : Nat)))) := by
      simp [sszLocal, evalHOLExact, hfirst, wordShiftHOL]
    have firstLe : first.toNat ≤ len.toNat := by have := ok.2.2; rw [BitVec.lt_def] at this; omega
    have cnt : (first >>> (2 : Nat)).toNat = first.toNat / 4 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have cntLe : (first >>> (2 : Nat)).toNat ≤ len.toNat / 4 := by rw [cnt]; exact Nat.div_le_div_right firstLe
    obtain ⟨nz, small⟩ := sszSplitFirst_count len first ok firstSmall
    apply evaluate_dec_word_R d (ofString "count") _ _ (first >>> (2 : Nat))
      (fun r t => ∀ v, r = some (.returned v) →
        SszSplitSlices d.memory d.memaddrs p len first pointer (first >>> (2 : Nat)) t.memory)
      (fun _ _ _ h => h) he
    generalize hc : setVarHOLFinite (ofString "count") (.val (.word (first >>> (2 : Nat)))) d = c
    have up : ∀ k, k ≠ ofString "count" → c.locals.lookup k = d.locals.lookup k := by
      intro k hk; rw [← hc]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
    have cc : c.clock = d.clock := by rw [← hc]; rfl
    have cm : c.memory = d.memory := by rw [← hc]; rfl
    have cd : c.memaddrs = d.memaddrs := by rw [← hc]; rfl
    intro v returned
    have slices := evaluate_sszSplitAllocStageB c p len first (first >>> (2 : Nat)) lim pointer
      ((up _ c1n.symm).trans hp) ((up _ c2n.symm).trans hlen) ((up _ c3n.symm).trans hfirst)
      (by rw [← hc]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) ((up _ c4n.symm).trans hlim)
      (by rw [← hc]; exact code) (by rw [← hc]; exact heap) pointerBound nz small (by omega) v returned
    rw [cm, cd] at slices
    exact slices

/-- Returned slice contract of the actual body, relative to the entry memory. -/
def SszSplitVarListSlicesReturned {σ : Type} (e : PanSemStateFiniteExact 64 σ) (p len pointer : BitVec 64)
    (post : PanSemStateFiniteExact 64 σ) : Prop :=
  (len = 0 ∧ post.memory = e.memory) ∨
  (∃ first, @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
      sszSplitFirst = some (.val (.word first)) ∧ first.toNat < 2 ^ 32 ∧
    SszSplitSlices e.memory e.memaddrs p len first pointer (first >>> (2 : Nat)) post.memory)

theorem evaluate_sszSplitVarList_slices_enough {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (p len lim pointer : BitVec 64) (installed : e.code = originalRuntimeCode)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word len)))
    (hlim : e.locals.lookup (ofString "lim") = some (.val (.word lim)))
    (heap : e.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (enough : sszSplitBound len ≤ e.clock) :
    ∀ v, (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_split_var_list)).1 = some (.returned v) →
      SszSplitVarListSlicesReturned e p len pointer
        (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_split_var_list)).2 := by
  unfold sszSplitBound at enough
  have f1 : ofString "first" ≠ ofString "p" := by decide_cbv
  have f2 : ofString "first" ≠ ofString "len" := by decide_cbv
  have f3 : ofString "first" ≠ ofString "lim" := by decide_cbv
  intro v returned
  rw [source_sszSplitVarList_body, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at returned ⊢
  by_cases zero : len = 0
  · subst zero
    have cond : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
        (.cmp .equal (sszLocal "len") (.const 0)) = some (.val (.word 1#64)) := by
      simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [cond]
    simp [evalHOLExact, evalListHOLExact, shapeOfHOLExact, emptyLocalsHOLFinite, SszSplitVarListSlicesReturned]
  · have cond : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
        (.cmp .equal (sszLocal "len") (.const 0)) = some (.val (.word 0#64)) := by
      simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      exact zero
    rw [cond] at returned ⊢
    dsimp only at returned ⊢
    rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip] at returned ⊢
    dsimp only at returned ⊢
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at returned ⊢
    by_cases short : len < 4
    · have cond4 : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
          (.cmp .lower (sszLocal "len") (.const 4)) = some (.val (.word 1#64)) := by
        simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact short
      rw [cond4] at returned
      dsimp only at returned
      rw [if_neg (by decide : ¬ (1#64 : BitVec 64) = 0)] at returned
      obtain ⟨x, run, abnormal, _, _⟩ := sszFail_abnormal e 20 installed (by omega)
      rw [run] at returned
      dsimp only at returned
      exact absurd (Option.some.inj (run.symm.trans returned)) (abnormal.2.2.2 v)
    · have cond4 : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
          (.cmp .lower (sszLocal "len") (.const 4)) = some (.val (.word 0#64)) := by
        simp [sszLocal, evalHOLExact, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact BitVec.not_lt.mp short
      rw [cond4] at returned ⊢
      dsimp only at returned ⊢
      rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip] at returned ⊢
      dsimp only at returned ⊢
      cases init : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a)) sszSplitFirst with
      | none =>
        rw [evaluateHOLFiniteState_dec_total] at returned
        dsimp only at returned
        simp only [init] at returned
        simp at returned
      | some value =>
        obtain ⟨first, rfl, firstSmall⟩ := @sszSplitFirst_bounded σ e.toExact (fun a => Classical.propDecidable (e.memaddrs a)) value init
        revert returned
        apply evaluate_dec_word_R e (ofString "first") _ _ first
          (fun r t => r = some (.returned v) → SszSplitVarListSlicesReturned e p len pointer t)
          (fun _ _ _ h => h) init
        generalize hd : setVarHOLFinite (ofString "first") (.val (.word first)) e = d
        have up : ∀ k, k ≠ ofString "first" → d.locals.lookup k = e.locals.lookup k := by
          intro k hk; rw [← hd]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        have dc : d.clock = e.clock := by rw [← hd]; rfl
        have dm : d.memory = e.memory := by rw [← hd]; rfl
        have dd : d.memaddrs = e.memaddrs := by rw [← hd]; rfl
        intro returned
        have slices := evaluate_sszSplitFirstStageB d p len first lim pointer
          ((up _ f1.symm).trans hp) ((up _ f2.symm).trans hlen)
          (by rw [← hd]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          ((up _ f3.symm).trans hlim) (by rw [← hd]; exact installed) (by rw [← hd]; exact heap) pointerBound
          firstSmall (by omega) v returned
        rw [dm, dd] at slices
        exact Or.inr ⟨first, init, firstSmall, slices⟩

#print axioms evaluate_sszSplitVarList_slices_enough

/-- At any clock, every return of the actual ssz_split_var_list satisfies the
slice-cell contract relative to the entry memory and domain. -/
theorem evaluate_sszSplitVarList_slices {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (p len lim pointer : BitVec 64) (installed : e.code = originalRuntimeCode)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word len)))
    (hlim : e.locals.lookup (ofString "lim") = some (.val (.word lim)))
    (heap : e.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) :
    ∀ v, (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_split_var_list)).1 = some (.returned v) →
      SszSplitVarListSlicesReturned e p len pointer
        (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_split_var_list)).2 := by
  intro v returned
  let out := evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
  let lifted : PanSemStateFiniteExact 64 σ := {e with clock := e.clock + sszSplitBound len}
  have run : evaluateHOLFiniteState lifted (sourceFunctionBody Guest.guestFn_ssz_split_var_list) =
      (out.1, {out.2 with clock := out.2.clock + sszSplitBound len}) :=
    panPropsEvaluateAddClockEq _ e out.1 out.2 _ ⟨rfl, by change out.1 ≠ _; rw [returned]; simp⟩
  have high := evaluate_sszSplitVarList_slices_enough lifted p len lim pointer installed hp hlen hlim heap
    pointerBound (by simp [lifted]) v (by rw [run]; exact returned)
  have he : @evalHOLExact 64 σ _ lifted.toExact (fun a => Classical.propDecidable (lifted.memaddrs a)) sszSplitFirst =
      @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a)) sszSplitFirst :=
    @evalHOLExact_upd_clock_eq 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a)) sszSplitFirst _
  rw [run] at high
  rcases high with ⟨a, b⟩ | ⟨first, hf, small, slices⟩
  · exact Or.inl ⟨a, b⟩
  · exact Or.inr ⟨first, he.symm.trans hf, small, slices⟩

#print axioms evaluate_sszSplitVarList_slices
end InitECandidate.Runtime
