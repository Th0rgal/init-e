import InitECandidate.Runtime.CeilLog2DeclarationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Any word input is covered by the real call bound. A successful return
supplies a depth at most 63 and its input-covering power of two. -/
theorem runBounded_ceilLog2_decCall {F : Type}
    (state : PanSemStateFiniteExact 64 F) (name : MlS) (argument : ExpHOL 64)
    (continuation : ProgHOL 64) (n : BitVec 64) (tailCost : Nat)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [argument] = some [.val (.word n)])
    (budget : 64 + 1 + tailCost ≤ state.clock)
    (tail : ∀ (d : BitVec 64) (post : PanSemStateFiniteExact 64 F), d.toNat ≤ 63 →
      n.toNat ≤ ((1#64) <<< d.toNat).toNat →
      post.code = state.code → post.memory = state.memory → post.memaddrs = state.memaddrs →
      post.be = state.be → post.globals = state.globals → tailCost ≤ post.clock →
      RunBounded (setVarHOLFinite name (.val (.word d)) {post with locals := state.locals}) continuation tailCost) :
    RunBounded state (.decCall name .one (ofString "ceil_log2") [argument] continuation)
      (64 + 1 + tailCost) := by
  refine RunBounded.decCall args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "ceil_log2") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_ceil_log2,.one) := by
    rw [code]
    exact originalRuntimeCode_ceilLog2_lookup
  rw [pan_single_word_lookup state.code.lookup (ofString "ceil_log2") (ofString "n")
    (sourceFunctionBody Guest.guestFn_ceil_log2) n installed] at lookup
  cases lookup
  constructor
  · exact RunBounded.ofProg ceilLog2_body_bounded code (by change 64 ≤ state.clock - 1; omega)
  · intro value post run remaining
    let entry := callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "n",.val (.word n)))
    have input : entry.locals.lookup (ofString "n") = some (.val (.word n)) := by
      simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    obtain ⟨d,small,valueEq,covers⟩ := ceilLog2_body_returned entry post n value input run
    have meta' := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ceil_log2)
    have memory := evaluate_readOnly_memory _ ceilLog2_readOnly entry
    have globals := evaluate_readOnly_globals _ ceilLog2_readOnly entry
    rw [run] at meta' memory globals
    rw [valueEq]
    exact tail d post (by omega) covers meta'.1 memory meta'.2.1 meta'.2.2.1 globals remaining

#print axioms runBounded_ceilLog2_decCall
end InitECandidate.Runtime
