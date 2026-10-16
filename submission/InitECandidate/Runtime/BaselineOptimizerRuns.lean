import InitECandidate.Runtime.BaselineOptimizerCode
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordProps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord

open Classical in
theorem optimizer_runs_same_clock {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (start k : Nat) (hrel : codeRel s.code l) (hnic : noInstallCode s.code)
    (hnac : noAllocCode s.code) (hnmc : noMtCode s.code) (hdom : sptDomain s.code = sptDomain l)
    (hgc : Compiler.Backend.WordSimp.gcFunConstOk s.gcFun) (hstack : s.stack = [])
    (hne : (evaluate (.call none (some start) [0] none) { s with clock := k }).1 ≠ some .error) :
    (evaluate (.call none (some start) [0] none) { s with clock := k, code := l }).1 =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).1 ∧
      (evaluate (.call none (some start) [0] none) { s with clock := k, code := l }).2.ffi =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).2.ffi ∧
      (evaluate (.call none (some start) [0] none) { s with clock := k, code := l }).2.clock =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).2.clock ∧
      (evaluate (.call none (some start) [0] none) { s with clock := k, code := l }).2.stackMax =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).2.stackMax := by
  let prog : WordLangProgHOL (BitVec width) := .call none (some start) [0] none
  let sk : WordSemStateFiniteExact width C F := { s with clock := k }
  obtain ⟨perm', H⟩ := panLang_compile_word_to_word_thm sk l start
    ⟨hrel, hnic, hnac, hnmc, hdom, hgc⟩
  have P3 := permute_swap_lemma3 prog sk perm' []
  rcases hE : evaluate prog sk with ⟨q, r⟩
  change (evaluate prog sk).1 ≠ some .error at hne
  rw [hE] at hne P3
  dsimp only at hne P3
  obtain ⟨perm'', stack', hP, -⟩ := P3 ⟨hne, hnac, rfl, hnic, rfl, by
    intro fr hfr
    change fr ∈ s.stack at hfr
    rw [hstack] at hfr
    cases hfr⟩
  dsimp only at H
  rw [hP] at H
  dsimp only at H
  rw [if_neg hne] at H
  rcases hT : evaluate prog { sk with code := l } with ⟨q1, r1⟩
  rw [hT] at H
  dsimp only at H
  obtain ⟨h1, h2, h3, h4⟩ := H
  exact ⟨h1, h3, h2, h4⟩

/-- Actual checked baseline optimization preserves every nonerror clocked run
at the same initial fuel. All code-related premises are proved internally. -/
theorem baseline_optimizer_run {C F : Type}
    (s : WordSemStateFiniteExact 64 C F) (fuel : Nat)
    (result : Option (WordSemResult 64)) (post : WordSemStateFiniteExact 64 C F)
    (code : s.code = sptFromAList FrontendStages.pass5)
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk s.gcFun) (empty : s.stack = [])
    (run : evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {s with clock := fuel} = (result,post)) (notError : result ≠ some .error) :
    ∃ final, evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {s with clock := fuel, code := sptFromAList BackendStages.Native.programs0} = (result,final) ∧
      final.ffi = post.ffi ∧ final.clock = post.clock ∧ final.stackMax = post.stackMax := by
  have rel := baseline_optimizer_codeRel
  have domain := baseline_optimizer_domain
  have ni := baseline_frontend_noInstall
  have na := baseline_frontend_noAlloc
  have nm := baseline_frontend_noMt
  rw [← code] at rel domain ni na nm
  have transferred := optimizer_runs_same_clock s (sptFromAList BackendStages.Native.programs0)
    BvlToBvi.initGlobalsLocation fuel rel ni na nm domain gc empty (by rw [run]; exact notError)
  rw [run] at transferred
  rcases targetRun : evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
    {s with clock := fuel, code := sptFromAList BackendStages.Native.programs0} with ⟨targetResult,final⟩
  rw [targetRun] at transferred
  dsimp only at transferred
  exact ⟨final, by rw [transferred.1], transferred.2⟩

#print axioms optimizer_runs_same_clock
#print axioms baseline_optimizer_run
end InitECandidate.Runtime
