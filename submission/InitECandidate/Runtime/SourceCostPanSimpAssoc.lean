import InitECandidate.Runtime.SourceCostPanSimpBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! `pan_simp$seq_assoc` never increases executed source work. The invariant
is stated against `SmartSeq pre p`, the program `seq_assoc pre p` stands for, so
re-association is free (`Seq` emits no event of its own). -/

theorem simp_seqAssoc_seq (pre a b : ProgHOL 64) :
    seqAssocHOL pre (.seq a b) = seqAssocHOL (seqAssocHOL pre a) b := by
  rw [seqAssocHOL]

/-- Running `SmartSeq pre (Seq a b)` splits into a run of `SmartSeq pre a`
followed (when it completes normally) by a run of `b`. -/
theorem simp_smartSeq_split {F : Type} {pre a b : ProgHOL 64} {s : PanSemStateFiniteExact 64 F}
    {r post ev} (run : StatementRun s (smartSeqHOL pre (.seq a b)) r post ev) :
    (∃ middle ev1 ev2, StatementRun s (smartSeqHOL pre a) none middle ev1 ∧
        StatementRun middle b r post ev2 ∧ SimpWorkLe (ev1 ++ ev2) ev) ∨
      (∃ ev1, r ≠ none ∧ StatementRun s (smartSeqHOL pre a) r post ev1 ∧ SimpWorkLe ev1 ev) := by
  by_cases hp : pre = .skip
  · subst hp
    cases run with
    | seqNext one two => exact Or.inl ⟨_, _, _, one, two, SimpWorkLe.refl _⟩
    | seqStop terminal one =>
      refine Or.inr ⟨_, terminal, one, fun c => ?_⟩
      (try simp only [executionWork_score_cons]); omega
  · rw [simp_smartSeq_ne _ hp] at run
    rw [simp_smartSeq_ne _ hp]
    cases run with
    | seqNext one two =>
      cases two with
      | seqNext a1 b1 =>
        refine Or.inl ⟨_, _, _, .seqNext one a1, b1, fun c => ?_⟩
        (try simp only [executionWork_score_cons, executionWork_score_append]); omega
      | seqStop terminal a1 =>
        refine Or.inr ⟨_, terminal, .seqNext one a1, fun c => ?_⟩
        (try simp only [executionWork_score_cons, executionWork_score_append]); omega
    | seqStop terminal one =>
      exact Or.inr ⟨_, terminal, .seqStop terminal one, SimpWorkLe.refl _⟩

theorem simp_seqAssoc_run {F : Type} :
    ∀ (p pre : ProgHOL 64), SimpRunLe (F := F) (smartSeqHOL pre p) (seqAssocHOL pre p)
  | .skip, pre => by
    unfold seqAssocHOL
    intro run
    rename_i s r post ev
    by_cases hp : pre = .skip
    · subst hp; exact ⟨ev, run, SimpWorkLe.refl _⟩
    · rw [simp_smartSeq_ne _ hp] at run
      cases run with
      | seqNext one two =>
        obtain ⟨rfl, rfl, rfl⟩ := simp_skip_run two
        refine ⟨_, one, fun c => ?_⟩
        (try simp only [executionWork_score_cons, executionWork_score_append]); omega
      | seqStop terminal one =>
        refine ⟨_, one, fun c => ?_⟩
        (try simp only [executionWork_score_cons]); omega
  | .annot tag text, pre => by
    unfold seqAssocHOL
    intro run
    rename_i s r post ev
    by_cases hp : pre = .skip
    · subst hp
      cases run
      exact ⟨_, .skip _, SimpWorkLe.refl _⟩
    · rw [simp_smartSeq_ne _ hp] at run
      cases run with
      | seqNext one two =>
        cases two
        refine ⟨_, one, fun c => ?_⟩
        (try simp only [executionWork_score_cons, executionWork_score_append]); omega
      | seqStop terminal one =>
        refine ⟨_, one, fun c => ?_⟩
        (try simp only [executionWork_score_cons]); omega
  | .seq a b, pre => by
    rw [simp_seqAssoc_seq]
    intro run
    rename_i s r post ev
    rcases simp_smartSeq_split run with ⟨middle, ev1, ev2, r1, r2, le⟩ | ⟨ev1, terminal, r1, le⟩
    · obtain ⟨evA, rA, leA⟩ := simp_seqAssoc_run a pre r1
      have comb : ∃ e, StatementRun s (smartSeqHOL (seqAssocHOL pre a) b) r post e ∧
          SimpWorkLe e (evA ++ ev2) := by
        by_cases hA : seqAssocHOL pre a = .skip
        · rw [hA] at rA ⊢
          obtain ⟨-, rfl, rfl⟩ := simp_skip_run rA
          refine ⟨ev2, r2, fun c => ?_⟩
          (try simp only [executionWork_score_cons, executionWork_score_append]); omega
        · rw [simp_smartSeq_ne _ hA]
          exact ⟨_, .seqNext rA r2, SimpWorkLe.refl _⟩
      obtain ⟨e, re, le2⟩ := comb
      obtain ⟨e', re', le3⟩ := simp_seqAssoc_run b (seqAssocHOL pre a) re
      refine ⟨e', re', fun c => ?_⟩
      have := le c; have := leA c; have := le2 c; have := le3 c
      try simp only [executionWork_score_cons, executionWork_score_append] at *
      omega
    · obtain ⟨evA, rA, leA⟩ := simp_seqAssoc_run a pre r1
      have hA : seqAssocHOL pre a ≠ .skip := by
        intro hA; rw [hA] at rA; exact terminal (simp_skip_run rA).1
      have re : StatementRun s (smartSeqHOL (seqAssocHOL pre a) b) r post evA := by
        rw [simp_smartSeq_ne _ hA] at ⊢
        exact .seqStop terminal rA
      obtain ⟨e', re', le3⟩ := simp_seqAssoc_run b (seqAssocHOL pre a) re
      refine ⟨e', re', fun c => ?_⟩
      have := le c; have := leA c; have := le3 c
      try simp only [executionWork_score_cons, executionWork_score_append] at *
      omega
  | .dec name shape value body, pre => by
    have e : seqAssocHOL pre (.dec name shape value body) =
        smartSeqHOL pre (.dec name shape value (seqAssocHOL .skip body)) := by rw [seqAssocHOL]
    rw [e]
    exact simp_smartSeq_congr (simp_dec_runs (simp_seqAssoc_run body .skip))
  | .ite condition yes no, pre => by
    have e : seqAssocHOL pre (.ite condition yes no) =
        smartSeqHOL pre (.ite condition (seqAssocHOL .skip yes) (seqAssocHOL .skip no)) := by
      rw [seqAssocHOL]
    rw [e]
    exact simp_smartSeq_congr (simp_ite_runs (simp_seqAssoc_run yes .skip)
      (simp_seqAssoc_run no .skip))
  | .while condition body, pre => by
    have e : seqAssocHOL pre (.while condition body) =
        smartSeqHOL pre (.while condition (seqAssocHOL .skip body)) := by rw [seqAssocHOL]
    rw [e]
    exact simp_smartSeq_congr (simp_while_runs (simp_seqAssoc_run body .skip))
  | .decCall name shape function arguments body, pre => by
    have e : seqAssocHOL pre (.decCall name shape function arguments body) =
        smartSeqHOL pre (.decCall name shape function arguments (seqAssocHOL .skip body)) := by
      rw [seqAssocHOL]
    rw [e]
    exact simp_smartSeq_congr (simp_decCall_runs (simp_seqAssoc_run body .skip))
  | .call none function arguments, pre => by
    have e : seqAssocHOL pre (.call none function arguments) =
        smartSeqHOL pre (.call (simpMapInfo (seqAssocHOL .skip) none) function arguments) := by
      rw [seqAssocHOL]; rfl
    rw [e]
    exact simp_smartSeq_congr (simp_call_runs _ (fun _ _ _ _ h => by cases h))
  | .call (some (returns, none)) function arguments, pre => by
    have e : seqAssocHOL pre (.call (some (returns, none)) function arguments) =
        smartSeqHOL pre (.call (simpMapInfo (seqAssocHOL .skip) (some (returns, none)))
          function arguments) := by
      rw [seqAssocHOL]; rfl
    rw [e]
    exact simp_smartSeq_congr (simp_call_runs _ (fun _ _ _ _ h => by cases h))
  | .call (some (returns, some (exception, handlerVar, handler))) function arguments, pre => by
    have e : seqAssocHOL pre (.call (some (returns, some (exception, handlerVar, handler)))
          function arguments) =
        smartSeqHOL pre (.call (simpMapInfo (seqAssocHOL .skip)
          (some (returns, some (exception, handlerVar, handler)))) function arguments) := by
      rw [seqAssocHOL]; rfl
    have ih : SimpRunLe (F := F) (smartSeqHOL .skip handler) (seqAssocHOL .skip handler) :=
      simp_seqAssoc_run handler .skip
    have hh : ∀ returns' exception' handlerVar' handler',
        some (returns, some (exception, handlerVar, handler)) =
          some (returns', some (exception', handlerVar', handler')) →
        SimpRunLe (F := F) handler' (seqAssocHOL .skip handler') := by
      intro r' e' v' h' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨-, -, -, rfl⟩ := heq
      exact ih
    rw [e]
    exact simp_smartSeq_congr (simp_call_runs _ hh)
  | .assign kind name value, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .primitive name operator args, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .store address value, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .store32 address value, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .storeByte address value, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .break, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .continue, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .extCall function configuration configurationLength array arrayLength, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .raise exception value, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .return value, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .shMemLoad size kind name address, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .shMemStore size address value, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
  | .tick, pre => by
    unfold seqAssocHOL; exact fun run => ⟨_, run, SimpWorkLe.refl _⟩
termination_by p => sizeOf p

#print axioms simp_seqAssoc_run
end InitECandidate.Runtime.FineCost
