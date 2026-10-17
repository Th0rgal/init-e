import InitECandidate.Runtime.MemcpyAlignmentValue
import InitECandidate.Runtime.MemcpyDispatchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original memcpy body budget, with unrestricted alignment and
contents and all memory-error outcomes included. -/
theorem evaluate_memcpy_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source size : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (small : size.toNat ≤ 33806089496)
    (budget : size.toNat / 32 + size.toNat / 8 + 10 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memcpy) = (result,post) ∧
      state.clock ≤ post.clock + (size.toNat / 32 + size.toNat / 8 + 10) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have locals : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atIndex : entered.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atSize := (locals _ (by decide)).trans sizeLocal
  obtain ⟨flag,condition⟩ := eval_memcpy_alignment_value entered destination source
    ((locals _ (by decide)).trans dstLocal) ((locals _ (by decide)).trans srcLocal)
  obtain ⟨result,post,run,cost,remaining,noTimeout⟩ := evaluate_memcpy_after_index_bounded entered 0 size flag
    atIndex atSize (by simp) small condition (by simpa [entered,setVarHOLFinite] using budget)
  let final := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "i",state.locals.lookup (ofString "i"))}
  refine ⟨result,final,?_,?_,remaining,noTimeout⟩
  · rw [source_memcpy_scoped_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let result := evaluateHOLFiniteState entered memcpyAfterIndex; _) = _
    rw [run]
  · change state.clock ≤ post.clock + (size.toNat / 32 + size.toNat / 8 + 10)
    simpa [entered,setVarHOLFinite] using cost

#print axioms evaluate_memcpy_body_bounded
end InitECandidate.Runtime
