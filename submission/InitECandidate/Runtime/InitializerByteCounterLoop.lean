import InitECandidate.Runtime.InitializerByteCounterStep
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def initializerByteCounterLoop (limit : BitVec 64) (destination value : ExpHOL 64) : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "i")) (.const limit)) (initializerByteCounterStep destination value)

def initializerByteCounterRank {F : Type} (limit : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => limit.toNat - index.toNat
  | _ => 0

/-- At most one source tick per remaining iteration, with byte-store faults
included. Below 2^63 the source's signed comparison follows the natural rank. -/
theorem evaluate_initializer_byte_counter_loop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (index limit : BitVec 64)
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (smallLimit : limit.toNat < 2^63) (inside : index.toNat ≤ limit.toNat) (budget : limit.toNat - index.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (initializerByteCounterLoop limit destination value) = (result,post) ∧
      state.clock ≤ post.clock + (limit.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → post.locals.lookup (ofString "i") = some (.val (.word limit))) ∧
      (∀ finalValue, result ≠ some (.returned finalValue)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => ∃ i : BitVec 64,
    current.locals.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ limit.toNat
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ i : BitVec 64,
      current.locals.lookup (ofString "i") = some (.val (.word i)) →
      initializerByteCounterRank limit current = limit.toNat - i.toNat := by
    intro current i binding
    simp [initializerByteCounterRank,binding]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a))
      (.cmp .less (.var .local (ofString "i")) (.const limit)) =
      some (.val (.word (if initializerByteCounterRank limit current = 0 then 0 else 1))) := by
    rintro current ⟨i,binding,bounded⟩
    have indexSign : i.toNat < 2^(64-1) := Nat.lt_of_le_of_lt bounded smallLimit
    have limitSign : limit.toNat < 2^(64-1) := smallLimit
    by_cases enabled : i.toNat < limit.toNat
    · have nonzero : limit.toNat - i.toNat ≠ 0 := by omega
      simp [evalHOLFinite,evalHOLExact,binding,Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess,indexSign,limitSign,BitVec.lt_def,
        enabled,rankEq current i binding,nonzero]
      omega
    · have zero : limit.toNat - i.toNat = 0 := by omega
      simp [evalHOLFinite,evalHOLExact,binding,Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess,indexSign,limitSign,BitVec.lt_def,
        enabled,rankEq current i binding,zero]
      omega
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨i,binding,bounded⟩
    exact ⟨i,binding,bounded⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      initializerByteCounterRank limit (decClockHOLFinite current) = initializerByteCounterRank limit current := by
    intro current
    rfl
  have step : ∀ current, invariant current → 0 < initializerByteCounterRank limit current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current (initializerByteCounterStep destination value) = (none,post) ∧ invariant post ∧
          initializerByteCounterRank limit post < initializerByteCounterRank limit current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ finalValue, result ≠ .returned finalValue) ∧
           evaluateHOLFiniteState current (initializerByteCounterStep destination value) = (some result,post))) := by
    rintro current ⟨i,binding,bounded⟩ positive _
    obtain ⟨result,post,run,clock,control⟩ := evaluate_initializer_byte_counter_step current destination value i binding
    refine ⟨post,by omega,by omega,?_⟩
    rcases control with ⟨rfl,advanced⟩ | rfl
    · rw [rankEq current i binding] at positive
      have natural : (i + 1).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by have width := limit.isLt; change i.toNat + 1 < 2^64; omega)]
        rfl
      refine Or.inl ⟨run,⟨i+1,advanced,by omega⟩,?_⟩
      rw [rankEq post (i+1) advanced,rankEq current i binding,natural]
      omega
    · exact Or.inr ⟨.error,by simp,by simp,by simp,(by intro finalValue; simp),run⟩
  obtain ⟨result,post,run,cost,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .less (.var .local (ofString "i")) (.const limit)) (initializerByteCounterStep destination value)
    invariant (initializerByteCounterRank limit) 0 guard enter entryRank step state ⟨index,atIndex,inside⟩
    (by simpa [rankEq state index atIndex] using budget)
  refine ⟨result,post,run,?_,remaining,noTimeout,?_,noReturn⟩
  · simpa [rankEq state index atIndex] using cost
  · intro normal
    obtain ⟨⟨i,binding,bounded⟩,zero⟩ := done normal
    rw [rankEq post i binding] at zero
    have equal : i = limit := BitVec.eq_of_toNat_eq (by omega)
    simpa only [equal] using binding

#print axioms evaluate_initializer_byte_counter_loop
end InitECandidate.Runtime
