import InitECandidate.Runtime.CeilLog2Returned
import InitECandidate.Runtime.NormalWhileInvariantByGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A power-of-two input bound caps the actual returned loop counter. -/
theorem ceilLog2_loop_small {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (n d : BitVec 64) (k : Nat) (small : k < 64)
    (inputBound : n.toNat ≤ ((1#64) <<< k).toNat)
    (input : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (counter : state.locals.lookup (ofString "d") = some (.val (.word d)))
    (initial : d.toNat ≤ k)
    (run : evaluateHOLFiniteState state (.while ceilLog2Condition ceilLog2Increment) = (none,post)) :
    ∃ result : BitVec 64, result.toNat ≤ k ∧
      post.locals.lookup (ofString "d") = some (.val (.word result)) := by
  let invariant := fun next : PanSemStateFiniteExact 64 F =>
    ∃ value : BitVec 64, next.locals.lookup (ofString "d") = some (.val (.word value)) ∧
      value.toNat ≤ k ∧ next.locals.lookup (ofString "n") = some (.val (.word n))
  have step : ∀ current next (word : BitVec 64), invariant current →
      evalHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a)) ceilLog2Condition =
        some (.val (.word word)) → word ≠ 0 →
      evaluateHOLFiniteState (decClockHOLFinite current) ceilLog2Increment = (none,next) → invariant next := by
    intro current next word valid guard running bodyRun
    obtain ⟨value,atCounter,within,atInput⟩ := valid
    have legal : ¬ (value.toNat ≠ 0 ∧ 64 ≤ value.toNat) := by omega
    have strict : ((1#64) <<< value.toNat).toNat < n.toNat := by
      by_contra notLess
      have notWordLess : ¬ ((1#64) <<< value.toNat) < n := by
        intro less
        have natural := BitVec.lt_def.mp less
        omega
      have zeroGuard : evalHOLFinite current
          (h := fun a => Classical.propDecidable (current.memaddrs a)) ceilLog2Condition =
          some (.val (.word (0#64))) := by
        simp [ceilLog2Condition,evalHOLFinite_eq_toExact,evalHOLExact,atCounter,atInput,
          wordShiftHOL,legal,Compiler.Encoders.Asm.wordCmpHOL,notWordLess]
      rw [zeroGuard] at guard
      have zero : word = (0 : BitVec 64) := by cases guard; rfl
      exact running zero
    have below : value.toNat < k := by
      by_contra notBelow
      have equal : value.toNat = k := by omega
      rw [equal] at strict
      omega
    rw [evaluate_ceilLog2_increment (decClockHOLFinite current) value atCounter] at bodyRun
    have nextEq := (Prod.mk.inj bodyRun).2
    rw [← nextEq]
    refine ⟨value + 1,?_,?_,?_⟩
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [BitVec.toNat_add_of_lt (by simp; omega)]
      change value.toNat + 1 ≤ k
      omega
    · simpa [setVarHOLFinite,decClockHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "d" ≠ ofString "n" by decide] using atInput
  have valid : invariant state := ⟨d,counter,initial,input⟩
  obtain ⟨result,binding,bounded,_⟩ := evaluate_normal_while_invariant_by_guard
    ceilLog2Condition ceilLog2Increment invariant step
    (fun current => evaluate_noLoopControl ceilLog2Increment (by rfl) current)
    state post valid run
  exact ⟨result,bounded,binding⟩

theorem ceilLog2_body_returned_small {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (n : BitVec 64) (value : ValueHOL 64) (k : Nat) (small : k < 64)
    (inputBound : n.toNat ≤ ((1#64) <<< k).toNat)
    (input : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_ceil_log2) =
      (some (.returned value),post)) :
    ∃ d : BitVec 64, d.toNat ≤ k ∧ value = .val (.word d) := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (.dec (ofString "d") .one (.const (0#64))
    (.seq (.while ceilLog2Condition ceilLog2Increment) (.return (.var .local (ofString "d"))))) = _ at run
  obtain ⟨middle,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "d") (.const (0#64))
    0 _ (some (.returned value)) rfl run
  let entered := setVarHOLFinite (ofString "d") (.val (.word (0#64))) state
  obtain ⟨loopPost,loopRun,binding⟩ := ceilLog2_return_exposes_loop entered middle value bodyRun
  obtain ⟨d,bounded,counter⟩ := ceilLog2_loop_small entered loopPost n 0 k small inputBound
    (by simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "d" ≠ ofString "n" by decide] using input)
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by simp) loopRun
  refine ⟨d,bounded,?_⟩
  rw [counter] at binding
  exact (Option.some.inj binding).symm

#print axioms ceilLog2_loop_small
#print axioms ceilLog2_body_returned_small
end InitECandidate.Runtime
