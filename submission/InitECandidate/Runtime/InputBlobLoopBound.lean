import InitECandidate.Runtime.InputBlobStep
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def inputBlobRank {F : Type} (length : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => (length.toNat + 7 - index.toNat) / 8
  | _ => 0

/-- The actual shared-input word-copy loop takes at most one source tick
per eight-byte chunk, including a partial final chunk and all failures. -/
theorem evaluate_inputBlob_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index length : BitVec 64)
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (inside : index.toNat ≤ length.toNat + 7) (small : length.toNat ≤ 134217712)
    (budget : (length.toNat + 7 - index.toNat) / 8 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state inputBlobLoop = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat + 7 - index.toNat) / 8 ∧ post.clock ≤ state.clock ∧
      result ≠ some .timeOut ∧
      (result = none → ∃ finalIndex : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        post.locals.lookup (ofString "len") = some (.val (.word length)) ∧
        length.toNat ≤ finalIndex.toNat ∧ finalIndex.toNat ≤ length.toNat + 7) ∧
      (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => ∃ i : BitVec 64,
    current.locals.lookup (ofString "i") = some (.val (.word i)) ∧
    current.locals.lookup (ofString "len") = some (.val (.word length)) ∧ i.toNat ≤ length.toNat + 7
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ i : BitVec 64,
      current.locals.lookup (ofString "i") = some (.val (.word i)) →
      inputBlobRank length current = (length.toNat + 7 - i.toNat) / 8 := by
    intro current i binding; simp [inputBlobRank,binding]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a)) inputBlobCondition =
        some (.val (.word (if inputBlobRank length current = 0 then 0 else 1))) := by
    rintro current ⟨i,localIndex,localLength,bounded⟩
    by_cases enabled : i.toNat < length.toNat
    · have nonzero : (length.toNat + 7 - i.toNat) / 8 ≠ 0 := by omega
      simp [inputBlobCondition,evalHOLFinite,evalHOLExact,localIndex,localLength,
        Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,enabled,rankEq current i localIndex,nonzero]
    · have zero : (length.toNat + 7 - i.toNat) / 8 = 0 := by omega
      simp [inputBlobCondition,evalHOLFinite,evalHOLExact,localIndex,localLength,
        Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,enabled,rankEq current i localIndex,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨i,localIndex,localLength,bounded⟩; exact ⟨i,localIndex,localLength,bounded⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      inputBlobRank length (decClockHOLFinite current) = inputBlobRank length current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < inputBlobRank length current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current inputBlobStep = (none,post) ∧ invariant post ∧
          inputBlobRank length post < inputBlobRank length current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current inputBlobStep = (some result,post))) := by
    rintro current ⟨i,localIndex,localLength,bounded⟩ positive _
    obtain ⟨result,post,run,clock,locals,normal⟩ := evaluate_inputBlob_step current i localIndex
    refine ⟨post,by omega,by omega,?_⟩
    rcases normal with ⟨rfl,advanced⟩ | rfl | ⟨event,rfl⟩
    · have natural : (i + 8).toNat = i.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt (by change i.toNat + 8 < 2 ^ 64; omega)]; rfl
      rw [rankEq current i localIndex] at positive
      refine Or.inl ⟨run,⟨i + 8,advanced,(locals rfl _ (by decide) (by decide)).trans localLength,by omega⟩,?_⟩
      rw [rankEq post (i + 8) advanced,rankEq current i localIndex,natural]
      omega
    · exact Or.inr ⟨.error,by simp,by simp,by simp,(by intro value; simp),run⟩
    · exact Or.inr ⟨.finalFfi event,by simp,by simp,by simp,(by intro value; simp),run⟩
  obtain ⟨result,post,run,spent,kept,safe,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    inputBlobCondition inputBlobStep invariant (inputBlobRank length) 0 guard enter entryRank step state
    ⟨index,atIndex,atLength,inside⟩ (by simpa [rankEq state index atIndex] using budget)
  refine ⟨result,post,run,?_,kept,safe,?_,noReturn⟩
  · simpa [rankEq state index atIndex] using spent
  · intro normal
    obtain ⟨⟨i,localIndex,localLength,bounded⟩,zero⟩ := done normal
    rw [rankEq post i localIndex] at zero
    exact ⟨i,localIndex,localLength,by omega,bounded⟩

#print axioms evaluate_inputBlob_loop_bounded
end InitECandidate.Runtime
