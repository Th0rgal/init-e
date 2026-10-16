import InitECandidate.Runtime.MemzeroAlignedFrameBody
import InitECandidate.Runtime.OriginalMemzeroCode
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original aligned memzero call, including argument binding and its
entry clock. A separate word is preserved and caller locals are restored. -/
theorem evaluate_memzero_aligned_frame_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destinationArgument sizeArgument : ExpHOL 64) (destination size watched : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [destinationArgument,sizeArgument] =
        some [.val (.word destination),.val (.word size)])
    (code : state.code = originalRuntimeCode) (budget : size.toNat + 1 ≤ state.clock)
    (small : destination.toNat + size.toNat ≤ 33806089496) (aligned : destination.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "memzero") [destinationArgument,sizeArgument]) = (none,post) ∧
      post.memory watched = state.memory watched ∧ state.clock ≤ post.clock + size.toNat + 1 ∧
      post.clock ≤ state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "dst",.val (.word destination))).update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have different : ofString "n" ≠ ofString "dst" := by decide
  have dstLocal : entry.locals.lookup (ofString "dst") = some (.val (.word destination)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have sizeLocal : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyPost,body,covered,cost,remaining,globals,postCode,domain,endian⟩ :=
    evaluate_source_memzero_aligned_frame entry destination size watched dstLocal sizeLocal small aligned
      (by change size.toNat ≤ state.clock - 1; omega) wordDomain wordSeparate byteSeparate byteDomain
  have installed : state.code.lookup (ofString "memzero") =
      some ([(ofString "dst",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memzero,.one) := by
    rw [code]; exact originalRuntimeCode_memzero_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "memzero") (ofString "dst") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memzero) destination size (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "memzero")
    [destinationArgument,sizeArgument] [.val (.word destination),.val (.word size)]
    (sourceFunctionBody Guest.guestFn_memzero) callee .one (.val (.word 0)) bodyPost
    arguments lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{bodyPost with locals := state.locals},call,covered,?_,?_,globals,postCode,domain,endian,rfl⟩
  · change state.clock ≤ bodyPost.clock + size.toNat + 1
    change state.clock - 1 ≤ bodyPost.clock + size.toNat at cost
    omega
  · change bodyPost.clock ≤ state.clock
    change bodyPost.clock ≤ state.clock - 1 at remaining
    omega

#print axioms evaluate_memzero_aligned_frame_call
end InitECandidate.Runtime
