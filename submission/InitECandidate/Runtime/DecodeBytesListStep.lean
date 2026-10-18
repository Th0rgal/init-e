import InitECandidate.Runtime.DecodeBytesListSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem bytesList_lenAddress_eval {σ : Type} (s : PanSemStateFiniteExact 64 σ) (arr count i : BitVec 64)
    (hr : s.locals.lookup (ofString "r") = some (.rStruct [.val (.word arr), .val (.word count)]))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i))) :
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) bytesListLenAddress =
      some (.val (.word (arr + i * 16#64 + 8#64))) := by
  simp [bytesListLenAddress, sszLocal, evalHOLExact, evalListHOLExact, hr, hi, wordOpHOL, wordOp, valueIsWord,
    valueWord, panOpHOL]
  exact (BitVec.add_assoc _ _ _).symm

/-- One length check: either slice i's length cell is readable and ≤ maxb and
i advances, or the iteration exits abnormally. -/
theorem bytesListStep_outcome {σ : Type} (s : PanSemStateFiniteExact 64 σ) (arr count i maxb : BitVec 64)
    (hr : s.locals.lookup (ofString "r") = some (.rStruct [.val (.word arr), .val (.word count)]))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hm : s.locals.lookup (ofString "maxb") = some (.val (.word maxb)))
    (code : s.code = originalRuntimeCode) (positive : s.clock ≠ 0) :
    let out := evaluateHOLFiniteState s bytesListStep
    s.clock ≤ out.2.clock + 1 ∧ out.2.clock ≤ s.clock ∧
      ((out.1 = none ∧ out.2 = setVarHOLFinite (ofString "i") (.val (.word (i + 1))) s ∧
          s.memaddrs (arr + i * 16#64 + 8#64) ∧ ¬ maxb < memWord s.memory (arr + i * 16#64 + 8#64)) ∨
       (∃ x, out.1 = some x ∧ SszAbnormal x)) := by
  have addr := bytesList_lenAddress_eval s arr count i hr hi
  unfold bytesListStep
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  by_cases dom : s.memaddrs (arr + i * 16#64 + 8#64)
  · by_cases bad : maxb < memWord s.memory (arr + i * 16#64 + 8#64)
    · have cond : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .lower (sszLocal "maxb") (.load .one bytesListLenAddress)) = some (.val (.word 1#64)) := by
        rw [evalHOLExact]
        simp [evalHOLExact, addr, sszLocal, hm, memLoadHOLExact, isWfShapeExactHOL, dom,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact bad
      rw [cond]
      dsimp only
      rw [if_neg (by decide : ¬ (1#64 : BitVec 64) = 0)]
      obtain ⟨x, run, abnormal, c1, c2⟩ := sszFail_abnormal s 70 code positive
      rw [run]
      dsimp only
      exact ⟨c1, c2, Or.inr ⟨x, run, abnormal⟩⟩
    · have cond : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .lower (sszLocal "maxb") (.load .one bytesListLenAddress)) = some (.val (.word 0#64)) := by
        rw [evalHOLExact]
        simp [evalHOLExact, addr, sszLocal, hm, memLoadHOLExact, isWfShapeExactHOL, dom,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact BitVec.not_lt.mp bad
      rw [cond]
      dsimp only
      rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip]
      dsimp only
      rw [sszSplit_assign_i s i hi]
      exact ⟨Nat.le_succ _, Nat.le_refl _, Or.inl ⟨rfl, rfl, dom, bad⟩⟩
  · have cond : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (sszLocal "maxb") (.load .one bytesListLenAddress)) = none := by
      rw [evalHOLExact]
      simp [evalHOLExact, addr, memLoadHOLExact, isWfShapeExactHOL, dom]
    rw [cond]
    exact ⟨Nat.le_succ _, Nat.le_refl _, Or.inr ⟨.error, rfl, by simp [SszAbnormal]⟩⟩

#print axioms bytesListStep_outcome
end InitECandidate.Runtime
