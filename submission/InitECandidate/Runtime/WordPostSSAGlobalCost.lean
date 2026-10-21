import InitECandidate.Runtime.WordPostSSALoopCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

theorem postSSA_leaf_transport {C F : Type} (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F) (leaf : WordToWord.cscLeaf program = true) :
    PostSSATransportAt program source := by
  intro _
  have framed := postSSACodeTable_leaf_execution program source leaf
  exact ⟨framed.1, le_of_eq framed.2⟩

/-- Whole-table optimizer transport. Calls use the concrete mapped table,
including indirect callees. The call hypotheses in the local cases are
fully discharged by global induction on termination depth and actual clock;
structural composition uses the source syntax size. -/
theorem postSSACodeTable_transport {C F : Type}
    (config : Compiler.Encoders.Asm.AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (free : noInstallSubprogsHOL program = true)
    (codeFree : WordProps.noInstallCode source.code) (codeFlat : PostSSAFlatCode source.code) :
    PostSSATransportAt program source := by
  cases program
  case seq first second =>
    have parts : noInstallSubprogsHOL first = true ∧ noInstallSubprogsHOL second = true := by
      simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] using free
    apply postSSA_seq_transport first second source parts.1 codeFree
    · exact postSSACodeTable_transport config first source parts.1 codeFree codeFlat
    · intro middle actual
      have clocks := evaluate_clock first source none middle actual
      have middleCode : middle.code = source.code := by
        have h := code_evaluate first source parts.1 codeFree
        simpa only [actual] using h
      exact postSSACodeTable_transport config second middle parts.2
        (middleCode.symm ▸ codeFree) (middleCode.symm ▸ codeFlat)
  case ite cmp reg operand first second =>
    have parts : noInstallSubprogsHOL first = true ∧ noInstallSubprogsHOL second = true := by
      simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] using free
    exact postSSA_ite_transport cmp reg operand first second source
      (postSSACodeTable_transport config first source parts.1 codeFree codeFlat)
      (postSSACodeTable_transport config second source parts.2 codeFree codeFlat)
  case mustTerminate body =>
    have bodyFree : noInstallSubprogsHOL body = true := by
      simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.true_and] using free
    apply postSSA_mustTerminate_transport body source
    intro positive
    exact postSSACodeTable_transport config body
      {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}
      bodyFree codeFree codeFlat
  case loop names body exits =>
    have bodyFree : noInstallSubprogsHOL body = true := by
      simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using free
    apply postSSA_loop_transport names exits body source bodyFree codeFree
    · intro cutSource cut
      have cutCode := cutState_code (names, .ln) source cutSource cut
      have clocks := cutState_clock_termdep (names, .ln) source cutSource cut
      exact postSSACodeTable_transport config body cutSource bodyFree
        (cutCode.symm ▸ codeFree) (cutCode.symm ▸ codeFlat)
    · intro cutSource result middle cut actual continuing positive
      have cutCode := cutState_code (names, .ln) source cutSource cut
      have cutFree : WordProps.noInstallCode cutSource.code := cutCode.symm ▸ codeFree
      have middleCode : middle.code = source.code := by
        have h := code_evaluate body cutSource bodyFree cutFree
        rw [actual] at h
        exact h.trans cutCode
      have clocks := evaluate_clock body cutSource result middle actual
      have cutClocks := cutState_clock_termdep (names, .ln) source cutSource cut
      exact postSSACodeTable_transport config (.loop names body exits) (decClock middle) free
        (middleCode.symm ▸ codeFree) (middleCode.symm ▸ codeFlat)
  case call returns destination arguments handler =>
    have calleeIH : PostSSACodeTransportIH (C := C) (F := F) source.termdep source.clock := by
      intro child childSource childPost childResult smaller childFree childCodeFree childFlat childRun childSafe
      have checked := postSSACodeTable_transport config child childSource childFree childCodeFree childFlat
        (by simpa only [childRun] using childSafe)
      simpa only [childRun] using checked
    rcases returns with _ | ⟨values, names, continuation, l1, l2⟩
    · rcases handler with _ | ⟨reg, handlerCode, h1, h2⟩
      · intro safe
        exact postSSACodeTable_tail_execution config destination arguments source codeFree codeFlat safe calleeIH
      · intro safe
        simp only [WordToWord.evaluate_call_eq] at safe
        repeat' split at safe
        all_goals exact (safe rfl).elim
    · intro safe
      apply postSSACodeTable_return_execution config values names continuation l1 l2
        destination arguments handler source codeFree codeFlat (noInstall_call_ret free) ?_ safe calleeIH
      intro reg handlerCode h1 h2 handlerEq
      subst handler
      exact noInstall_call_handler free
  case install =>
    simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.false_eq_true] at free
  all_goals
    apply postSSA_leaf_transport
    rfl
termination_by (source.termdep, source.clock, sizeOf program)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, decClock]
  all_goals omega

/-- Concrete whole post-SSA stage endpoint: transform every callee body and
the entry program, construct the actual target run and bound its executed
work with coefficient one. Locals may differ only at fall-through/loop-control
outcomes, exactly as in the local dead-code elimination contract. -/
theorem postSSA_code_table_cost {C F : Type}
    (config : Compiler.Encoders.Asm.AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64)) (source post : WordSemStateFiniteExact 64 C F)
    (result : Option (WordSemResult 64)) (free : noInstallSubprogsHOL program = true)
    (flat : flatExpConventions program = true) (codeFree : WordProps.noInstallCode source.code)
    (codeFlat : PostSSAFlatCode source.code) (run : evaluate program source = (result, post))
    (safe : result ≠ some .error) :
    ∃ locals,
      evaluate (postSSAOptimize program) {source with code := postSSACodeTable source.code} =
        (result, {post with code := postSSACodeTable source.code, locals := locals}) ∧
      RemoveDeadProgPost result post.locals locals ∧
      wordExecutionCost wordOptimizerLocalPrice (postSSAOptimize program)
        {source with code := postSSACodeTable source.code} ≤
      wordExecutionCost wordOptimizerLocalPrice program source := by
  obtain ⟨transported, transportCost⟩ := postSSACodeTable_transport config program source free codeFree codeFlat
    (by simpa only [run] using safe)
  rw [run] at transported
  obtain ⟨locals, optimized, related, cost⟩ := postSSAOptimize_executed_correct config program
    {source with code := postSSACodeTable source.code} {post with code := postSSACodeTable source.code}
    result flat transported safe
  exact ⟨locals, optimized, related, cost.trans transportCost⟩

#print axioms postSSACodeTable_transport
#print axioms postSSA_code_table_cost
end InitECandidate.Runtime.FineCost
