import InitECandidate.Runtime.RlpListCountLoopInvariant
import InitECandidate.Runtime.RlpListCountStepBound
import InitECandidate.Runtime.RlpListCountStepControl
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpListCountLoop : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_list_count with
  | .dec _ _ _ (.dec _ _ _ (.seq loop _)) => loop
  | _ => .skip

theorem source_rlpListCount_loop : rlpListCountLoop =
    .while (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))) rlpListCountStep := by
  simp only [rlpListCountLoop,rlpListCountStep,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def rlpListCountRank {F : Type} (length : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "off") with
  | some (.val (.word offset)) => length.toNat - offset.toNat
  | _ => 0

/-- The complete original list-count loop has a finite remaining-input clock
budget. Normal completion exhausts the input, bounds the count and retains
scratch/frame globals; all early failures are covered without timeout. -/
theorem evaluate_rlpListCount_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : RlpListCountLoopWitness state pointer length scratch frame ceiling)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (budget : (length.toNat - valid.offset.toNat) * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpListCountLoop = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat - valid.offset.toNat) * ((2 * length.toNat + 1) * 15 + 19) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ count : BitVec 64,
        post.locals.lookup (ofString "off") = some (.val (.word length)) ∧
        post.locals.lookup (ofString "count") = some (.val (.word count)) ∧ count.toNat ≤ length.toNat ∧
        post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame))) ∧
      (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => Nonempty (RlpListCountLoopWitness current pointer length scratch frame ceiling)
  let cost := (2 * length.toNat + 1) * 15 + 18
  have rankEq : ∀ (current : PanSemStateFiniteExact 64 F) (witness : RlpListCountLoopWitness current pointer length scratch frame ceiling),
      rlpListCountRank length current = length.toNat - witness.offset.toNat := by
    intro current witness
    simp [rlpListCountRank,witness.offsetLocal]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun address => Classical.propDecidable (current.memaddrs address))
      (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))) =
      some (.val (.word (if rlpListCountRank length current = 0 then 0 else 1))) := by
    rintro current ⟨witness⟩
    by_cases inside : witness.offset.toNat < length.toNat
    · have nonzero : rlpListCountRank length current ≠ 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.offsetLocal,witness.lengthLocal,
        Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,nonzero]
    · have zero : rlpListCountRank length current = 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.offsetLocal,witness.lengthLocal,
        Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨witness⟩
    exact ⟨witness.decClock⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      rlpListCountRank length (decClockHOLFinite current) = rlpListCountRank length current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < rlpListCountRank length current → cost ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + cost ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current rlpListCountStep = (none,post) ∧ invariant post ∧
          rlpListCountRank length post < rlpListCountRank length current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current rlpListCountStep = (some result,post))) := by
    rintro current ⟨witness⟩ _ ticks
    have bounded := evaluate_rlpListCount_step_bounded current pointer length witness.offset scratch frame ceiling inputLimit
      witness.pointerLocal witness.lengthLocal witness.offsetLocal witness.offsetBound noWrap lengthBound limitBound
      witness.scratchGlobal witness.frameGlobal witness.code orderedFrame framePositive scratchBelow witness.arena ticks
    have control := evaluate_rlpListCount_step_control current
    cases run : evaluateHOLFiniteState current rlpListCountStep with
    | mk result post =>
      rw [run] at bounded control
      refine ⟨post,bounded.1,bounded.2.1,?_⟩
      cases result with
      | none =>
        obtain ⟨next,decreases⟩ := rlpListCount_loop_witness_step current post pointer length scratch frame ceiling inputLimit
          witness noWrap lengthBound limitBound orderedFrame framePositive scratchBelow ticks run
        exact Or.inl ⟨rfl,⟨next⟩,by rw [rankEq post next,rankEq current witness]; exact decreases⟩
      | some result =>
        refine Or.inr ⟨result,?_,?_,?_,?_,rfl⟩
        · intro equal; subst result; exact control.2.1 rfl
        · intro equal; subst result; exact bounded.2.2 rfl
        · intro equal; subst result; exact control.1 rfl
        · intro value equal; subst result; exact control.2.2 value rfl
  obtain ⟨result,post,run,total,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))) rlpListCountStep
    invariant (rlpListCountRank length) cost guard enter entryRank step state ⟨valid⟩
    (by simpa only [rankEq state valid,cost] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · rw [source_rlpListCount_loop]; exact run
  · simpa only [rankEq state valid,cost] using total
  · intro normal
    obtain ⟨⟨next⟩,zero⟩ := done normal
    have same : next.offset = length := by
      apply BitVec.eq_of_toNat_eq
      rw [rankEq post next] at zero
      have bounded := next.offsetBound
      omega
    exact ⟨next.count,by simpa [same] using next.offsetLocal,next.countLocal,
      by have a := next.countBound; have b := next.offsetBound; omega,next.scratchGlobal,next.frameGlobal⟩

#print axioms evaluate_rlpListCount_loop_bounded
end InitECandidate.Runtime
