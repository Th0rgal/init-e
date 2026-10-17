import InitECandidate.Runtime.MemcpyByte8LoopBound
import InitECandidate.Runtime.MemcpyByte1LoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memcpyByteSuffix : ProgHOL 64 :=
  .seq memcpyByte8Loop (.seq memcpyByte1Loop (.return (.const 0)))

/-- Both byte-copy loops and the final return have a finite common budget,
including every malformed-memory exit, without alignment assumptions. -/
theorem evaluate_memcpy_byte_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) / 8 + 7 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memcpyByteSuffix = (result,post) ∧
      state.clock ≤ post.clock + ((size.toNat - index.toNat) / 8 + 7) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  obtain ⟨result,middle,run,cost,remaining,noTimeout,done,_⟩ := evaluate_memcpy_byte8_loop_bounded
    state index size indexLocal sizeLocal inside small (by omega)
  cases result with
  | some stopped =>
    refine ⟨some stopped,middle,?_,by omega,remaining,noTimeout⟩
    rw [memcpyByteSuffix,evaluateHOLFiniteState_seq_line780,run]
  | none =>
    obtain ⟨finalIndex,atIndex,atSize,bounded,remainder⟩ := done rfl
    obtain ⟨result,post,tail,tailCost,tailRemaining,tailNoTimeout,_,_⟩ := evaluate_memcpy_byte1_loop_bounded
      middle finalIndex size atIndex atSize bounded small (by omega)
    cases result with
    | some stopped =>
      refine ⟨some stopped,post,?_,by omega,by omega,tailNoTimeout⟩
      rw [memcpyByteSuffix,evaluateHOLFiniteState_seq_line780,run]
      dsimp only
      rw [evaluateHOLFiniteState_seq_line780,tail]
    | none =>
      have returned : evaluateHOLFiniteState post (.return (.const 0)) =
          (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
        simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
      refine ⟨some (.returned (.val (.word 0))),emptyLocalsHOLFinite post,?_,?_,?_,by simp⟩
      · rw [memcpyByteSuffix,evaluateHOLFiniteState_seq_line780,run]
        dsimp only
        rw [evaluateHOLFiniteState_seq_line780,tail]
        exact returned
      · change state.clock ≤ post.clock + ((size.toNat - index.toNat) / 8 + 7)
        omega
      · change post.clock ≤ state.clock
        omega

#print axioms evaluate_memcpy_byte_suffix_bounded
end InitECandidate.Runtime
