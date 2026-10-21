import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateConsts
import InitECandidate.Runtime.WordCodeFrameBounds
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordProps Flapjack.WordSemStateFiniteExact
variable {width : Nat} [NeZero width] {C F : Type}

private theorem stackSize_alloc (w : BitVec width) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) : (alloc w names s).2.stackSize = s.stackSize := by
  have facts := allocCodeGcFunConst w names s (alloc w names s).2 (alloc w names s).1 rfl
  aesop (config := { enableSimp := false })

private theorem stackSize_shareInst (op : WordMemOp) (v : Nat) (c : BitVec width)
    (s : WordSemStateFiniteExact width C F) : (shareInst (rw := width) op v c s).2.stackSize = s.stackSize := by
  cases op <;>
    simp only [shareInst,shMemSetVar,shMemLoad,shMemLoadByte,shMemLoad16,shMemLoad32,
      shMemStore,shMemStoreByte,shMemStore16,shMemStore32] <;>
    (repeat' split) <;> rfl

private theorem stackSize_evaluate_const (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true)
    (hni : noInstallSubprogsHOL p = true) :
    (evaluate p s).2.stackSize = s.stackSize := by
  cases p <;> simp only [wordProgClockConst,Bool.false_eq_true] at hp <;> rw [evaluate] <;>
    (repeat' split) <;>
    first
      | rfl
      | exact stackSize_alloc _ _ _
      | exact stackSize_shareInst _ _ _ _
      | (rename_i h; have facts := instConstFull _ _ _ h; aesop (config := {enableSimp := false}))
      | (rename_i h; have facts := memStoreConst _ _ _ _ h; aesop (config := {enableSimp := false}))
      | (rename_i h; have facts := jumpExcConst _ _ _ h; aesop (config := {enableSimp := false}))
      | (simp [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp] at hni)

private theorem stackSize_pushEnv (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) : (pushEnv envs handler s).stackSize = s.stackSize := by
  rcases handler with _ | ⟨_,_,_,_⟩ <;> rfl

theorem stackSize_evaluate :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      noInstallSubprogsHOL p = true → noInstallCode s.code → (evaluate p s).2.stackSize = s.stackSize
  | .tick, s, _, _ => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      split <;> rfl
  | .mustTerminate q, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.true_and] at hni
      by_cases hz : s.termdep = 0
      · simp only [hz, dite_true, if_true]
      · simp only [hz, dite_false, if_false]
        have ih := stackSize_evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } hni hc
        rcases hq : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        rw [hq] at ih
        cases r with
        | none => exact ih
        | some x => cases x <;> first | rfl | exact ih
  | .seq c1 c2, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hni
      have ih1 := stackSize_evaluate c1 s hni.1 hc
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at ih1
      have hc1 := evaluate_clock c1 s r1 s1 h1
      cases r1 with
      | none =>
        have hc' : noInstallCode s1.code := by
          have eq := code_evaluate c1 s hni.1 hc
          rw [h1] at eq
          exact eq ▸ hc
        exact (stackSize_evaluate c2 s1 hni.2 hc').trans ih1
      | some x => exact ih1
  | .ite cmp r1 ri c1 c2, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hni
      rcases getVar r1 s with _ | x <;> rcases getVarImm ri s with _ | y <;> simp only
      rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only <;>
        first | rfl | exact stackSize_evaluate c1 s hni.1 hc | exact stackSize_evaluate c2 s hni.2 hc
  | .loop names c exitNames, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hni' := hni
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni'
      rcases hcs : cutState (names, .ln) s with _ | s'
      · rfl
      simp only
      obtain ⟨l, rfl⟩ := cutStateConst _ _ _ hcs
      have hc2 := cutState_clock_termdep _ _ _ hcs
      have ih := stackSize_evaluate c { s with locals := l } hni' hc
      rcases hb : evaluate c { s with locals := l } with ⟨rb, s1⟩
      rw [hb] at ih
      have hcl := evaluate_clock c _ rb s1 hb
      simp only
      by_cases hcont : wordSemContLoop rb = true
      · simp only [hcont, if_true]
        by_cases hz : s1.clock = 0
        · simp only [hz, dite_true, if_true]
          exact ih
        · simp only [hz, dite_false, if_false, wordSemSTOP]
          have hcd : noInstallCode (decClock s1).code := by
              have eq := code_evaluate c {s with locals := l} hni' hc
              rw [hb] at eq
              exact eq ▸ hc
          exact (stackSize_evaluate (.loop names c exitNames) (decClock s1) hni hcd).trans ih
      · simp only [hcont, Bool.false_eq_true, if_false]
        split
        · split
          · exact ih
          · rename_i s2 hce
            obtain ⟨_, rfl⟩ := cutStateConst _ _ _ hce
            exact ih
        · exact ih
  | .call ret dest args handler, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht]
      rcases hg : getVars args s with _ | xs
      · rfl
      simp only
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true]
      simp only [hbad, Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · rfl
      simp only
      have hprog := noInstallFindCode s.code dest _ _ _ prog _ ⟨hc, hf⟩
      cases ret with
      | none =>
        cases handler with
        | some _ => rfl
        | none =>
          simp only
          by_cases hz : s.clock = 0
          · simp only [hz, dite_true, if_true]; rfl
          simp only [hz, dite_false, if_false]
          have ih := stackSize_evaluate prog (callEnv args1 ss (decClock s)) hprog hc
          rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          rw [hcv] at ih
          simp only
          split
          · exact ih
          · exact ih
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp only [hdc, if_true]
        simp only [hdc, if_false]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · rfl
        simp only
        by_cases hz : s.clock = 0
        · simp only [hz, dite_true, if_true]; rfl
        simp only [hz, dite_false, if_false]
        have hpre : (callEnv args1 ss (pushEnv envs handler (decClock s))).stackSize = s.stackSize :=
          stackSize_pushEnv envs handler _
        have ih := stackSize_evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))
          hprog (by simpa only [WordSemStateFiniteExact.callEnv,code_pushEnv,decClock] using hc)
        rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with
          ⟨rc, s2⟩
        rw [hcv] at ih
        have hcl := evaluate_clock prog _ rc s2 hcv
        have h2 : s2.stackSize = s.stackSize := ih.trans hpre
        have originalCode := code_evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))
          hprog (by simpa only [WordSemStateFiniteExact.callEnv,code_pushEnv,decClock] using hc)
        rw [hcv] at originalCode
        have h2Code : s2.code = s.code := originalCode.trans (code_pushEnv envs handler _)
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
        · exact h2
        · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp only [hx, if_true]; exact h2
          simp only [hx, if_false]
          rcases hp : popEnv s2 with _ | s1
          · exact h2
          simp only
          have h3 : s1.stackSize = s.stackSize := ((popEnvCodeGcFunClock _ _ hp).2.2.2.2.2.2.2.2.2.2.2.2.symm).trans h2
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          split
          · have hcs1 : noInstallCode (setVars n ys s1).code := by
                have eq := (popEnvCodeGcFunClock _ _ hp).1.symm.trans h2Code
                exact eq ▸ hc
            exact (stackSize_evaluate retHandler (setVars n ys s1) (noInstall_call_ret hni) hcs1).trans h3
          · exact h3
        · cases handler with
          | none => exact h2
          | some hv =>
            obtain ⟨n', hprog', l1', l2'⟩ := hv
            simp only
            split
            · exact h2
            · split
              · have hcs2 : noInstallCode (setVar n' y s2).code := h2Code ▸ hc
                exact (stackSize_evaluate hprog' (setVar n' y s2) (noInstall_call_handler hni) hcs2).trans h2
              · exact h2
        all_goals exact h2
  | .skip, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .move a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .inst a, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .assign a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .get a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .set a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .store a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .alloc a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .storeConsts a b c d f, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .raise a, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | WordLangProgHOL.return a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | WordLangProgHOL.break a, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | WordLangProgHOL.continue a, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .opCurrHeap a b c, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .locValue a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .install a b c d f, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .codeBufferWrite a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .dataBufferWrite a b, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .ffi a b c d f g, s, hni, _ => stackSize_evaluate_const s _ rfl hni
  | .shareInst a b c, s, hni, _ => stackSize_evaluate_const s _ rfl hni
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc1 with ⟨_, _⟩)
    try (rcases hcl with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try simp only [WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.callEnv,
      WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar, pushEnv_clock, pushEnv_termdep,
      true_and] at *
    omega


/-- A reached post-state retains declaration coverage and the original
frame bound. Both code and frame-map equalities follow from execution. -/
theorem CodeFramesBounded.after_evaluate
    {program : WordLangProgHOL (BitVec width)}
    {source post : WordSemStateFiniteExact width C F}
    {result : Option (WordSemResult width)} {limit : Nat}
    (covered : CodeFramesBounded source.code source.stackSize limit)
    (noInstall : noInstallSubprogsHOL program = true)
    (codeNoInstall : noInstallCode source.code)
    (run : evaluate program source = (result,post)) :
    CodeFramesBounded post.code post.stackSize limit := by
  have codeEq := code_evaluate program source noInstall codeNoInstall
  have frameEq := stackSize_evaluate program source noInstall codeNoInstall
  rw [run] at codeEq frameEq
  exact covered.transport codeEq frameEq

/-- Cutting locals changes neither map used by frame eligibility. -/
theorem CodeFramesBounded.after_cutState
    {source cut : WordSemStateFiniteExact width C F}
    {names : WordLangCutsetsHOL} {limit : Nat}
    (covered : CodeFramesBounded source.code source.stackSize limit)
    (run : cutState names source = some cut) :
    CodeFramesBounded cut.code cut.stackSize limit := by
  obtain ⟨locals,rfl⟩ := cutStateConst names source cut run
  exact covered

/-- Restoring a caller environment preserves the code and frame maps. -/
theorem CodeFramesBounded.after_popEnv
    {source popped : WordSemStateFiniteExact width C F} {limit : Nat}
    (covered : CodeFramesBounded source.code source.stackSize limit)
    (run : popEnv source = some popped) :
    CodeFramesBounded popped.code popped.stackSize limit := by
  have facts := popEnvCodeGcFunClock source popped run
  exact covered.transport facts.1.symm facts.2.2.2.2.2.2.2.2.2.2.2.2.symm

#print axioms stackSize_evaluate
#print axioms CodeFramesBounded.after_evaluate
#print axioms CodeFramesBounded.after_cutState
#print axioms CodeFramesBounded.after_popEnv
end InitECandidate.Runtime.WordToStack
