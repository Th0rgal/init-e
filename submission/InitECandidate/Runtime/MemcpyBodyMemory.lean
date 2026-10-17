import InitECandidate.Runtime.MemcpyBodyBound
import InitECandidate.Runtime.MemcpyDispatchMemory
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem memcpy_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (destination source size watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (small : size.toNat ≤ 33806089496)
    (budget : size.toNat / 32 + size.toNat / 8 + 10 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memcpy) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have locals : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atIndex : entered.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atSize := (locals _ (by decide)).trans sizeLocal
  obtain ⟨flag,condition⟩ := eval_memcpy_alignment_value entered destination source
    ((locals _ (by decide)).trans dstLocal) ((locals _ (by decide)).trans srcLocal)
  rw [source_memcpy_scoped_body] at run
  obtain ⟨output,tail,restored⟩ := evaluate_dec_word_result_scope state post (ofString "i") (.const 0) 0
    memcpyAfterIndex (some (.returned value)) (by rfl) run
  have kept := memcpy_after_index_returned_memory entered output destination source 0 size flag watched
    ((locals _ (by decide)).trans dstLocal) ((locals _ (by decide)).trans srcLocal) wordSeparate byteSeparate
    atIndex atSize (by simp) small condition (by simpa [entered,setVarHOLFinite] using budget) value tail
  rw [restored]
  exact kept

#print axioms memcpy_body_returned_memory
end InitECandidate.Runtime
