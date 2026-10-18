import InitECandidate.Runtime.MemcpyAlignedCall
import InitECandidate.Runtime.MemcpyAlignedBodyCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_memcpy_aligned_call_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destinationArgument sourceArgument sizeArgument : ExpHOL 64)
    (destination source size capacity used : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (aligned : destination.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0) (budget : size.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → offset % 8 = 0 → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < size.toNat → offset % 8 = 0 → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (code : state.code = originalRuntimeCode)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [destinationArgument,sourceArgument,sizeArgument] =
        some [.val (.word destination),.val (.word source),.val (.word size)]) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy")
        [destinationArgument,sourceArgument,sizeArgument]) = (none,post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used) ∧
      state.clock ≤ post.clock + size.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word destination))).update
      (ofString "src",.val (.word source))).update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have nd : ofString "n" ≠ ofString "dst" := by decide
  have ns : ofString "n" ≠ ofString "src" := by decide
  have sd : ofString "src" ≠ ofString "dst" := by decide
  have dst : entry.locals.lookup (ofString "dst") = some (.val (.word destination)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,nd,sd]
  have src : entry.locals.lookup (ofString "src") = some (.val (.word source)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,ns]
  have n : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,body,count,cost,remaining,globals,postCode,addresses,endian⟩ :=
    evaluate_source_memcpy_aligned_cells entry destination source size capacity used dst src n small aligned sourceAligned
      (by change size.toNat ≤ state.clock - 1; omega) wordDomain byteDomain sourceWordDomain sourceByteDomain wordSeparate byteSeparate
  have installed : state.code.lookup (ofString "memcpy") =
      some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memcpy,.one) := by
    rw [code]; exact originalRuntimeCode_memcpy_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "memcpy") (ofString "dst") (ofString "src") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memcpy) destination source size (by decide) (by decide) (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "memcpy")
    [destinationArgument,sourceArgument,sizeArgument] [.val (.word destination),.val (.word source),.val (.word size)]
    (sourceFunctionBody Guest.guestFn_memcpy) callee .one (.val (.word 0)) post arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{post with locals := state.locals},call,count,?_,?_,globals,postCode,addresses,endian,rfl⟩
  · change state.clock ≤ post.clock + size.toNat + 1
    change state.clock - 1 ≤ post.clock + size.toNat at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms evaluate_memcpy_aligned_call_cells
end InitECandidate.Runtime
