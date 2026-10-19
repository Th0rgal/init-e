import InitECandidate.Runtime.ValidateHeadersSecondLoopBound
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 40000
set_option maxHeartbeats 3000000

/-- The actual `At 5` phase of `validate_headers` in one piece: the real
`i := 1` reset, the real second loop, and the real `return (hs, hashes)`. -/
theorem source_validate_headers_second_phase :
    validateHeadersSecondAt 5 = .seq (.assign .local (ofString "i") (.const 1))
      (.seq (.while validateHeadersSecondCondition validateHeadersSecondBody)
        validateHeadersSecondReturn) := rfl

/-- The uniform tick budget of that phase: the reset and the return are
straight line (0 ticks), and the loop fits in `256 * 130` under the source cap
`n <= 256`. -/
def validateHeadersSecondPhaseCost : Nat := 256 * 130

/-- The real `i := 1` reset, run on any state whose `i` local is a word. -/
theorem evaluate_validate_headers_second_reset {F : Type} (s : PanSemStateFiniteExact 64 F)
    (givenIndex : BitVec 64)
    (atI : s.locals.lookup (ofString "i") = some (.val (.word givenIndex))) :
    evaluateHOLFiniteState s (.assign .local (ofString "i") (.const 1)) =
      (none,setVarHOLFinite (ofString "i") (.val (.word 1)) s) :=
  evaluate_local_word_assignment s (ofString "i") (.const 1) givenIndex 1 atI
    (by simp [evalHOLExact])

/-- The real second loop exits at once, spending no tick, when the freshly
reset index `1` is not below the count (in particular for `n = 0`). -/
theorem evaluate_validate_headers_second_loop_at_zero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (n : BitVec 64)
    (atI : s.locals.lookup (ofString "i") = some (.val (.word 1)))
    (atN : s.locals.lookup (ofString "n") = some (.val (.word n))) (empty : n = 0) :
    evaluateHOLFiniteState s validateHeadersSecondLoop = (none,s) := by
  have condition : evalHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address))
      validateHeadersSecondCondition = some (.val (.word 0)) := by
    subst empty
    simp [validateHeadersSecondCondition,evalHOLExact,evalListHOLExact,atI,atN,
      Compiler.Encoders.Asm.wordCmpHOL,valueIsWord,valueWord,Compiler.Encoders.Asm.holAsmSignedLess]
  rw [validateHeadersSecondLoop,evaluateHOLFiniteState_while_total,condition]
  simp

/-- Every outcome of the actual `At 5` phase — the real `i := 1` reset, the
real second loop and the real `return (hs, hashes)` — fits in the uniform
`33280`-tick budget.  The only premises are the original code, the typed
existing locals `i` (any word) and `n` (the count), the source cap `n <= 256`
and the tick budget: nothing about memory, the header table, `hs`/`hashes` or
the compared bytes is used, so failed loads and unusable windows are inside
the bound. -/
theorem runBounded_validate_headers_second_phase {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n givenIndex : BitVec 64)
    (atI : s.locals.lookup (ofString "i") = some (.val (.word givenIndex)))
    (atN : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (cap : n.toNat ≤ 256) (code : s.code = originalRuntimeCode)
    (budget : validateHeadersSecondPhaseCost ≤ s.clock) :
    RunBounded s (validateHeadersSecondAt 5) validateHeadersSecondPhaseCost := by
  change RunBounded s (validateHeadersSecondAt 5) (256 * 130)
  change 256 * 130 ≤ s.clock at budget
  have reset := evaluate_validate_headers_second_reset s givenIndex atI
  have resetBounded : RunBounded s (.assign .local (ofString "i") (.const 1)) 0 :=
    RunBounded.ofProg (ProgBounded.straight _ (by decide)) code (by omega)
  rw [source_validate_headers_second_phase]
  refine RunBounded.seq (a := 0) (b := 256 * 130) resetBounded (by omega) ?_
  intro start ran startCode resetBudget
  -- identify the state produced by the real reset
  have reflStart : start = setVarHOLFinite (ofString "i") (.val (.word 1)) s :=
    (Prod.mk.inj (ran.symm.trans reset)).2
  subst reflStart
  have startedAtI : (setVarHOLFinite (ofString "i") (.val (.word 1)) s).locals.lookup (ofString "i") =
      some (.val (.word 1)) := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have startedAtN : (setVarHOLFinite (ofString "i") (.val (.word 1)) s).locals.lookup (ofString "n") =
      some (.val (.word n)) := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      (by decide : ¬ ((ofString "n") = (ofString "i"))),(by decide : ¬ ((ofString "i") = (ofString "n"))),atN]
  have startedCode : (setVarHOLFinite (ofString "i") (.val (.word 1)) s).code = originalRuntimeCode := code
  have startedClock : (setVarHOLFinite (ofString "i") (.val (.word 1)) s).clock = s.clock := rfl
  have startedBudget : 256 * 130 ≤ (setVarHOLFinite (ofString "i") (.val (.word 1)) s).clock := by
    rw [startedClock]
    exact resetBudget
  have returnBounded : RunBounded (setVarHOLFinite (ofString "i") (.val (.word 1)) s)
      validateHeadersSecondReturn 0 :=
    RunBounded.ofProg (ProgBounded.straight _ (by decide)) startedCode (Nat.zero_le _)
  by_cases empty : n.toNat = 0
  · -- nothing to compare: the real loop exits at once and the return is free
    have nZero : n = 0 := BitVec.eq_of_toNat_eq (by simpa using empty)
    have resetLoop := evaluate_validate_headers_second_loop_at_zero
      (setVarHOLFinite (ofString "i") (.val (.word 1)) s) n startedAtI startedAtN nZero
    have enough : 256 * 130 + 0 ≤ (setVarHOLFinite (ofString "i") (.val (.word 1)) s).clock := by
      have := startedBudget
      omega
    refine RunBounded.seq (a := 256 * 130) (b := 0) ?_ enough ?_
    · show RunBounded (setVarHOLFinite (ofString "i") (.val (.word 1)) s) validateHeadersSecondLoop (256 * 130)
      unfold RunBounded
      rw [resetLoop]
      dsimp only
      rw [startedClock]
      exact ⟨by omega,le_refl _,by simp⟩
    · intro next ran' nextCode nextBudget
      rw [show (ProgHOL.while validateHeadersSecondCondition validateHeadersSecondBody) = validateHeadersSecondLoop
        from rfl] at ran'
      rw [resetLoop] at ran'
      have same : next = setVarHOLFinite (ofString "i") (.val (.word 1)) s := ((Prod.mk.inj ran').2).symm
      subst same
      exact returnBounded
  · -- the count is positive, so the real ranked invariant starts at i = 1
    have positive : 1 ≤ n.toNat := by omega
    have counted : ValidateHeadersSecondCount n (setVarHOLFinite (ofString "i") (.val (.word 1)) s)
        (n.toNat - 1) := by
      refine ⟨1,startedAtI,startedAtN,?_,cap,?_⟩
      · show (1 : BitVec 64).toNat ≤ n.toNat
        rw [show (1 : BitVec 64).toNat = 1 from rfl]
        omega
      · show n.toNat - 1 = n.toNat - (1 : BitVec 64).toNat
        rw [show (1 : BitVec 64).toNat = 1 from rfl]
    have loopBounded := runBounded_validate_headers_second_loop_cap
      (setVarHOLFinite (ofString "i") (.val (.word 1)) s) n (n.toNat - 1) startedCode counted startedBudget
    have enough : 256 * 130 + 0 ≤ (setVarHOLFinite (ofString "i") (.val (.word 1)) s).clock := by
      have := startedBudget
      omega
    refine RunBounded.seq (a := 256 * 130) (b := 0) ?_ enough ?_
    · show RunBounded (setVarHOLFinite (ofString "i") (.val (.word 1)) s) validateHeadersSecondLoop (256 * 130)
      exact loopBounded
    · intro next ran' nextCode nextBudget
      exact RunBounded.ofProg (ProgBounded.straight validateHeadersSecondReturn (by decide))
        (nextCode.trans startedCode) (by omega)

#print axioms source_validate_headers_second_phase
#print axioms evaluate_validate_headers_second_reset
#print axioms evaluate_validate_headers_second_loop_at_zero
#print axioms runBounded_validate_headers_second_phase
end InitECandidate.Runtime
