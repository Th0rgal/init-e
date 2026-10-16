import InitECandidate.Runtime.MemcpyAlignedCall
import InitECandidate.Runtime.MemcpyAlignedFrameCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The same actual copy execution preserves occupancy count and every
separate memory word; determinism identifies the independently proved states. -/
theorem evaluate_memcpy_aligned_call_with_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destinationArgument sourceArgument sizeArgument : ExpHOL 64)
    (destination source size capacity used : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (aligned : destination.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0) (budget : size.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
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
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals ∧
      ∀ watched : BitVec 64,
        (∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset) →
        (∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) →
        post.memory watched = state.memory watched := by
  obtain ⟨post,run,count,cost,remaining,globals,postCode,addresses,endian,locals⟩ :=
    evaluate_memcpy_aligned_call state destinationArgument sourceArgument sizeArgument destination source size capacity used
      small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain wordSeparate byteSeparate code arguments
  refine ⟨post,run,count,cost,remaining,globals,postCode,addresses,endian,locals,?_⟩
  intro watched words bytes
  obtain ⟨framed,frameRun,memory,_,_,_,_,_,_,_⟩ :=
    evaluate_memcpy_aligned_frame_call state destinationArgument sourceArgument sizeArgument destination source size watched
      small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain words bytes code arguments
  have equal : post = framed := congrArg Prod.snd (run.symm.trans frameRun)
  rw [equal]
  exact memory

#print axioms evaluate_memcpy_aligned_call_with_frame
end InitECandidate.Runtime
