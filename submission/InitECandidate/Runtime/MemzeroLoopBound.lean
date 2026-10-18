import InitECandidate.Runtime.StoreAdvanceBlockLoop
import InitECandidate.Runtime.StoreAdvanceTailLoop
import InitECandidate.Runtime.MemzeroAlignedSuffix
import InitECandidate.Runtime.MemzeroSyntax
import InitECandidate.Runtime.MemzeroAlignedBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem memzeroWord32Body_supported : StoreAdvanceStep (ofString "i") 32 memzeroWord32Body := by
  unfold memzeroWord32Body memzeroAdvance
  repeat (first | exact StoreAdvanceStep.advance | apply StoreAdvanceStep.store)

theorem memzeroWord8Body_supported : StoreAdvanceStep (ofString "i") 8 memzeroWord8Body := by
  unfold memzeroWord8Body memzeroAdvance
  repeat (first | exact StoreAdvanceStep.advance | apply StoreAdvanceStep.store)

theorem memzeroByte8Body_supported : StoreAdvanceStep (ofString "i") 8 memzeroByte8Body := by
  unfold memzeroByte8Body
  repeat (first | exact StoreAdvanceStep.advance | apply StoreAdvanceStep.storeByte | apply StoreAdvanceStep.store)

theorem memzeroByte1Body_supported : StoreAdvanceStep (ofString "i") 1 memzeroByte1Body := by
  unfold memzeroByte1Body memzeroAdvance
  repeat (first | exact StoreAdvanceStep.advance | apply StoreAdvanceStep.storeByte)

theorem evaluate_memzero_byte8_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) / 8 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memzeroByte8Loop = (result,post) ∧
      state.clock ≤ post.clock + (size.toNat - index.toNat) / 8 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ finalIndex : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word size)) ∧
        finalIndex.toNat ≤ size.toNat ∧ size.toNat - finalIndex.toNat < 8) ∧
      (∀ value, result ≠ some (.returned value)) := by
  rw [memzeroByte8Loop_shape]
  exact evaluate_storeAdvance_block8_loop_bounded state index size memzeroByte8Body memzeroByte8Body_supported
    indexLocal sizeLocal inside small budget

theorem eval_memzero_alignment_value {F : Type} (state : PanSemStateFiniteExact 64 F) (destination : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination))) :
    ∃ flag : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) memzeroAlignmentCondition = some (.val (.word flag)) := by
  exact ⟨_,by simp [memzeroAlignmentCondition,evalHOLExact,evalListHOLExact,dstLocal,wordOpHOL,wordOp,valueIsWord,valueWord]; rfl⟩

theorem evaluate_memzero_word_prefix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) / 32 + 3 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (.seq (.while (memzeroBlockCondition 32) memzeroWord32Body) (.while (memzeroBlockCondition 8) memzeroWord8Body)) = (result,post) ∧
      state.clock ≤ post.clock + ((size.toNat - index.toNat) / 32 + 3) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ finalIndex : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word size)) ∧
        finalIndex.toNat ≤ size.toNat ∧ size.toNat - finalIndex.toNat < 8) ∧
      (∀ value, result ≠ some (.returned value)) := by
  obtain ⟨result,middle,run,cost,remaining,noTimeout,done,noReturn⟩ := evaluate_storeAdvance_block32_loop_bounded
    state index size memzeroWord32Body memzeroWord32Body_supported indexLocal sizeLocal inside small (by omega)
  cases result with
  | some stopped =>
    refine ⟨some stopped,middle,?_,by omega,remaining,noTimeout,(by intro impossible; cases impossible),noReturn⟩
    rw [evaluateHOLFiniteState_seq_line780,run]
  | none =>
    obtain ⟨nextIndex,atIndex,atSize,bounded,remainder⟩ := done rfl
    obtain ⟨result,post,tail,tailCost,tailRemaining,tailNoTimeout,tailDone,tailNoReturn⟩ := evaluate_storeAdvance_block8_loop_bounded
      middle nextIndex size memzeroWord8Body memzeroWord8Body_supported atIndex atSize bounded small (by omega)
    refine ⟨result,post,?_,by omega,by omega,tailNoTimeout,tailDone,tailNoReturn⟩
    rw [evaluateHOLFiniteState_seq_line780,run]
    exact tail


def memzeroByteSuffix : ProgHOL 64 :=
  .seq memzeroByte8Loop (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) memzeroByte1Body) (.return (.const 0)))

/-- Both byte-zeroing loops and the final return have a finite common budget,
including every malformed-memory exit, without alignment assumptions. -/
theorem evaluate_memzero_byte_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) / 8 + 7 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memzeroByteSuffix = (result,post) ∧
      state.clock ≤ post.clock + ((size.toNat - index.toNat) / 8 + 7) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  obtain ⟨result,middle,run,cost,remaining,noTimeout,done,_⟩ := evaluate_memzero_byte8_loop_bounded
    state index size indexLocal sizeLocal inside small (by omega)
  cases result with
  | some stopped =>
    refine ⟨some stopped,middle,?_,by omega,remaining,noTimeout⟩
    rw [memzeroByteSuffix,evaluateHOLFiniteState_seq_line780,run]
  | none =>
    obtain ⟨finalIndex,atIndex,atSize,bounded,remainder⟩ := done rfl
    obtain ⟨result,post,tail,tailCost,tailRemaining,tailNoTimeout,_,_⟩ := evaluate_storeAdvance_tail1_loop_bounded
      middle finalIndex size memzeroByte1Body memzeroByte1Body_supported atIndex atSize bounded small (by omega)
    cases result with
    | some stopped =>
      refine ⟨some stopped,post,?_,by omega,by omega,tailNoTimeout⟩
      rw [memzeroByteSuffix,evaluateHOLFiniteState_seq_line780,run]
      dsimp only
      rw [evaluateHOLFiniteState_seq_line780,tail]
    | none =>
      have returned : evaluateHOLFiniteState post (.return (.const 0)) =
          (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
        simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
      refine ⟨some (.returned (.val (.word 0))),emptyLocalsHOLFinite post,?_,?_,?_,by simp⟩
      · rw [memzeroByteSuffix,evaluateHOLFiniteState_seq_line780,run]
        dsimp only
        rw [evaluateHOLFiniteState_seq_line780,tail]
        exact returned
      · change state.clock ≤ post.clock + ((size.toNat - index.toNat) / 8 + 7)
        omega
      · change post.clock ≤ state.clock
        omega


theorem evaluate_memzero_after_index_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size flag : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      memzeroAlignmentCondition = some (.val (.word flag)))
    (budget : (size.toNat - index.toNat) / 32 + (size.toNat - index.toNat) / 8 + 10 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memzeroAfterIndex = (result,post) ∧
      state.clock ≤ post.clock + ((size.toNat - index.toNat) / 32 + (size.toNat - index.toNat) / 8 + 10) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  change ∃ result post, evaluateHOLFiniteState state
    (.seq (.ite memzeroAlignmentCondition (.seq (.while (memzeroBlockCondition 32) memzeroWord32Body) (.while (memzeroBlockCondition 8) memzeroWord8Body)) .skip) memzeroByteSuffix) = (result,post) ∧ _
  by_cases zero : flag = 0
  · have branch : evaluateHOLFiniteState state (.ite memzeroAlignmentCondition (.seq (.while (memzeroBlockCondition 32) memzeroWord32Body) (.while (memzeroBlockCondition 8) memzeroWord8Body)) .skip) = (none,state) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp only [if_pos zero,evaluateHOLFiniteState_skip]
    obtain ⟨result,post,run,cost,remaining,noTimeout⟩ := evaluate_memzero_byte_suffix_bounded state index size indexLocal sizeLocal inside small (by omega)
    refine ⟨result,post,?_,by omega,remaining,noTimeout⟩
    rw [evaluateHOLFiniteState_seq_line780,branch]
    exact run
  · have branch : evaluateHOLFiniteState state (.ite memzeroAlignmentCondition (.seq (.while (memzeroBlockCondition 32) memzeroWord32Body) (.while (memzeroBlockCondition 8) memzeroWord8Body)) .skip) =
        evaluateHOLFiniteState state (.seq (.while (memzeroBlockCondition 32) memzeroWord32Body) (.while (memzeroBlockCondition 8) memzeroWord8Body)) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp only [if_neg zero]
    obtain ⟨result,middle,run,cost,remaining,noTimeout,done,_⟩ := evaluate_memzero_word_prefix_bounded state index size indexLocal sizeLocal inside small (by omega)
    cases result with
    | some stopped =>
      refine ⟨some stopped,middle,?_,by omega,remaining,noTimeout⟩
      rw [evaluateHOLFiniteState_seq_line780,branch,run]
    | none =>
      obtain ⟨nextIndex,atIndex,atSize,bounded,remainder⟩ := done rfl
      obtain ⟨result,post,tail,tailCost,tailRemaining,tailNoTimeout⟩ := evaluate_memzero_byte_suffix_bounded
        middle nextIndex size atIndex atSize bounded small (by omega)
      refine ⟨result,post,?_,by omega,by omega,tailNoTimeout⟩
      rw [evaluateHOLFiniteState_seq_line780,branch,run]
      exact tail


#print axioms evaluate_memzero_after_index_bounded
end InitECandidate.Runtime
