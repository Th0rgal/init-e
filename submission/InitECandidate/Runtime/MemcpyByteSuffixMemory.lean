import InitECandidate.Runtime.MemcpyByteSuffixBound
import InitECandidate.Runtime.MemcpyByte8LoopMemoryBound
import InitECandidate.Runtime.MemcpyByte1LoopMemoryBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successfully returned byte-copy suffix retains any separate memory word
without assumptions about source alignment or accessible source bytes. -/
theorem memcpy_byte_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (destination source index size watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (separate : ∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) / 8 + 7 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state memcpyByteSuffix = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  obtain ⟨result,middle,first,cost,_,_,done,noReturn⟩ := evaluate_memcpy_byte8_loop_memory_bounded
    state destination source index size watched dstLocal srcLocal separate indexLocal sizeLocal inside small (by omega)
  rw [memcpyByteSuffix,evaluateHOLFiniteState_seq_line780,first] at run
  cases result with
  | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)
  | none =>
    obtain ⟨finalIndex,atIndex,atSize,bounded,remainder,atDst,atSrc,firstFrame⟩ := done rfl
    obtain ⟨result,last,second,_,_,_,lastDone,lastNoReturn⟩ := evaluate_memcpy_byte1_loop_memory_bounded
      middle destination source finalIndex size watched atDst atSrc separate atIndex atSize bounded small (by omega)
    dsimp only at run
    rw [evaluateHOLFiniteState_seq_line780,second] at run
    cases result with
    | some stopped => exact False.elim (lastNoReturn value (Prod.mk.inj run).1)
    | none =>
      obtain ⟨_,_,_,_,_,_,_,lastFrame⟩ := lastDone rfl
      have returned : evaluateHOLFiniteState last (.return (.const 0)) =
          (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite last) := by
        simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
      have same := (Prod.mk.inj (run.symm.trans returned)).2
      rw [same]
      exact lastFrame.trans firstFrame

#print axioms memcpy_byte_suffix_returned_memory
end InitECandidate.Runtime
