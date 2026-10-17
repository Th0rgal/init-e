import InitECandidate.Runtime.MemcpyWordPrefixMemoryBound
import InitECandidate.Runtime.MemcpyByteSuffixMemory
import InitECandidate.Runtime.MemcpyDispatchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem memcpy_after_index_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (destination source index size flag watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      memcpyAlignmentCondition = some (.val (.word flag)))
    (budget : (size.toNat - index.toNat) / 32 + (size.toNat - index.toNat) / 8 + 10 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state memcpyAfterIndex = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  change evaluateHOLFiniteState state
    (.seq (.ite memcpyAlignmentCondition (.seq memcpyWord32Loop memcpyWord8Loop) .skip) memcpyByteSuffix) = _ at run
  by_cases zero : flag = 0
  · have branch : evaluateHOLFiniteState state (.ite memcpyAlignmentCondition (.seq memcpyWord32Loop memcpyWord8Loop) .skip) = (none,state) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp only [if_pos zero,evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_seq_line780,branch] at run
    exact memcpy_byte_suffix_returned_memory state post destination source index size watched dstLocal srcLocal byteSeparate
      indexLocal sizeLocal inside small (by omega) value run
  · have branch : evaluateHOLFiniteState state (.ite memcpyAlignmentCondition (.seq memcpyWord32Loop memcpyWord8Loop) .skip) =
        evaluateHOLFiniteState state (.seq memcpyWord32Loop memcpyWord8Loop) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp only [if_neg zero]
    obtain ⟨result,middle,first,cost,_,_,done,noReturn⟩ := evaluate_memcpy_word_prefix_memory_bounded
      state destination source index size watched dstLocal srcLocal wordSeparate indexLocal sizeLocal inside small (by omega)
    rw [evaluateHOLFiniteState_seq_line780,branch,first] at run
    cases result with
    | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)
    | none =>
      obtain ⟨nextIndex,atIndex,atSize,bounded,remainder,atDst,atSrc,saved⟩ := done rfl
      have kept := memcpy_byte_suffix_returned_memory middle post destination source nextIndex size watched atDst atSrc byteSeparate
        atIndex atSize bounded small (by omega) value run
      exact kept.trans saved

#print axioms memcpy_after_index_returned_memory
end InitECandidate.Runtime
