import InitECandidate.Runtime.KeccakShortInput
import InitECandidate.Runtime.HtabGrowFrame
import InitECandidate.Runtime.KeccakAbsorbCallBound
import InitECandidate.Runtime.RankedWhile
import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.NormalLocalAddCalls
import InitECandidate.Runtime.NoLoopControl
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def keccakFullCondition : ExpHOL 64 :=
  .cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 136])
def keccakFullArguments : List (ExpHOL 64) :=
  [.var .local (ofString "stp"),.op .add [.var .local (ofString "p"),.var .local (ofString "i")]]

theorem source_keccak_main_body : keccakMainLoopBody =
    .seq (.call (some (none,none)) (ofString "keccak_absorb_block") keccakFullArguments)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 136])) := by
  simp only [keccakMainLoopBody,keccakMainLoop,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem keccak_main_body_add : NormalLocalAdd (ofString "i") 136 keccakMainLoopBody := by
  rw [source_keccak_main_body]
  apply normalLocalAdd_seq_normal_frame
  · intro F state post run
    have keep := evaluate_avoidsLocal_flowing (ofString "i")
      (.call (some (none,none)) (ofString "keccak_absorb_block") keccakFullArguments) rfl state
      (by rw [run]; exact Or.inl rfl)
    rw [run] at keep
    exact keep
  · exact normalLocalAdd_assign _ _

def KeccakMainRank (pointer source size : BitVec 64) {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ∃ index : BitVec 64,
    state.locals.lookup (ofString "i") = some (.val (.word index)) ∧
    state.locals.lookup (ofString "n") = some (.val (.word size)) ∧
    state.locals.lookup (ofString "p") = some (.val (.word source)) ∧
    state.locals.lookup (ofString "stp") = some (.val (.word pointer)) ∧
    index.toNat ≤ size.toNat ∧ index.toNat % 8 = 0 ∧ rank = size.toNat - index.toNat

theorem eval_keccak_full_condition {F : Type} (state : PanSemStateFiniteExact 64 F) (index size : BitVec 64)
    (atI : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 134217712) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) keccakFullCondition =
      some (.val (.word (if index.toNat + 136 ≤ size.toNat then 1 else 0))) := by
  have natural : (index + (136#64)).toNat = index.toNat + 136 := word_add_toNat index 136 (by omega)
  simp [evalHOLFinite_eq_toExact,keccakFullCondition,evalHOLExact,evalListHOLExact,atI,atN,
    wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,natural]

/-- Every full-block iteration costs at most 20 clocks, including absorption
errors and external outcomes. The index cannot wrap under the challenge input cap. -/
theorem keccak_main_loop_ranked (pointer source size : BitVec 64) (small : size.toNat ≤ 134217712) :
    ∀ rank : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      KeccakMainRank pointer source size state rank → rank * 20 ≤ state.clock →
      RankedOutcome state keccakFullCondition (rank * 20) (KeccakMainRank pointer source size) False
        (evaluateHOLFiniteState state keccakMainLoop) := by
  have exit : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), KeccakMainRank pointer source size state 0 →
      ∀ w : BitVec 64, evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) keccakFullCondition =
        some (.val (.word w)) → w = 0 := by
    intro F state ⟨index,atI,atN,atP,atStp,inside,aligned,ranking⟩ w cond
    rw [eval_keccak_full_condition state index size atI atN inside small] at cond
    have inactive : ¬ index.toNat + 136 ≤ size.toNat := by omega
    simpa [inactive] using cond.symm
  have step : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat) (w : BitVec 64),
      state.code = originalRuntimeCode → KeccakMainRank pointer source size state (rank + 1) →
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) keccakFullCondition = some (.val (.word w)) →
      w ≠ 0 → 19 + 1 ≤ state.clock →
      state.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite state) keccakMainLoopBody).2.clock + 19 ∧
      (evaluateHOLFiniteState (decClockHOLFinite state) keccakMainLoopBody).2.clock ≤ state.clock - 1 ∧
      (evaluateHOLFiniteState (decClockHOLFinite state) keccakMainLoopBody).1 ≠ some .timeOut ∧
      ((evaluateHOLFiniteState (decClockHOLFinite state) keccakMainLoopBody).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite state) keccakMainLoopBody).1 = some .continue →
        ∃ m, m ≤ rank ∧ KeccakMainRank pointer source size (evaluateHOLFiniteState (decClockHOLFinite state) keccakMainLoopBody).2 m ∧
          (evaluateHOLFiniteState (decClockHOLFinite state) keccakMainLoopBody).2.code = state.code) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite state) keccakMainLoopBody).1 = some .break → False ∧
        ∃ m, KeccakMainRank pointer source size (evaluateHOLFiniteState (decClockHOLFinite state) keccakMainLoopBody).2 m ∧
          (evaluateHOLFiniteState (decClockHOLFinite state) keccakMainLoopBody).2.code = state.code) := by
    intro F state rank w code ⟨index,atI,atN,atP,atStp,inside,aligned,ranking⟩ cond nz budget
    have active : index.toNat + 136 ≤ size.toNat := by
      rw [eval_keccak_full_condition state index size atI atN inside small] at cond
      by_contra inactive
      simp [inactive] at cond
      exact nz (by simpa using cond.symm)
    let current := decClockHOLFinite state
    have args : evalListHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a)) keccakFullArguments =
        some [.val (.word pointer),.val (.word (source + index))] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [current,decClockHOLFinite,keccakFullArguments,evalListHOLExact,evalHOLExact,atP,atI,atStp,wordOpHOL,wordOp,valueIsWord,valueWord]
    have first : RunBounded current (.call (some (none,none)) (ofString "keccak_absorb_block") keccakFullArguments) 19 :=
      evaluate_keccakAbsorb_call_bounded current _ _ pointer (source + index) code args (by change 19 ≤ state.clock - 1; omega)
    have bounded : RunBounded current keccakMainLoopBody 19 := by
      rw [source_keccak_main_body]
      have whole := RunBounded.seq (tail := .assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 136])) (b := 0) first (by change 19 + 0 ≤ state.clock - 1; omega)
        (by intro next normal nextCode remaining; exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans code) remaining)
      simpa only [Nat.add_zero] using whole
    have control := evaluate_noLoopControl keccakMainLoopBody (by rw [source_keccak_main_body]; decide) current
    refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
    · intro continuing
      have normal : (evaluateHOLFiniteState current keccakMainLoopBody).1 = none := by
        rcases continuing with normal | impossible
        · exact normal
        · exact False.elim (control.2 impossible)
      have run : evaluateHOLFiniteState current keccakMainLoopBody = (none,(evaluateHOLFiniteState current keccakMainLoopBody).2) :=
        Prod.ext normal rfl
      have advanced := keccak_main_body_add current _ index atI run
      have keep (key : MlS) (different : key ≠ ofString "i") :
          (evaluateHOLFiniteState current keccakMainLoopBody).2.locals.lookup key = state.locals.lookup key := by
        have avoids : avoidsLocal key keccakMainLoopBody = true := by
          rw [source_keccak_main_body]
          simp [avoidsLocal,Ne.symm different]
        exact evaluate_avoidsLocal_flowing key keccakMainLoopBody avoids current (Or.inl normal)
      have natural : (index + (136#64)).toNat = index.toNat + 136 := word_add_toNat index 136 (by omega)
      have metadata := evaluateHOLFiniteState_metadata current keccakMainLoopBody
      refine ⟨size.toNat - (index + (136#64)).toNat,?_,?_,metadata.1⟩
      · rw [natural]; omega
      · refine ⟨index + (136#64),advanced,(keep _ (by decide)).trans atN,(keep _ (by decide)).trans atP,
          (keep _ (by decide)).trans atStp,(by rw [natural]; omega),?_,rfl⟩
        rw [natural,Nat.add_mod,aligned]
    · intro impossible
      exact False.elim (control.1 impossible)
  intro rank F state code valid budget
  rw [source_keccak_main_loop]
  exact rankedWhile_run keccakFullCondition keccakMainLoopBody 19 (KeccakMainRank pointer source size) False exit step rank state code valid budget

#print axioms source_keccak_main_body
#print axioms keccak_main_body_add
#print axioms eval_keccak_full_condition
#print axioms keccak_main_loop_ranked
end InitECandidate.Runtime
