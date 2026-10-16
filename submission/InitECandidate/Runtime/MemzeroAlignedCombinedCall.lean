import InitECandidate.Runtime.MemzeroAlignedCall
import InitECandidate.Runtime.MemzeroAlignedFrameCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One actual zeroing call establishes zero coverage and preserves all
separate memory words; determinism identifies both execution summaries. -/
theorem evaluate_memzero_aligned_call_with_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destinationArgument sizeArgument : ExpHOL 64) (destination size : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [destinationArgument,sizeArgument] =
        some [.val (.word destination),.val (.word size)])
    (code : state.code = originalRuntimeCode) (budget : size.toNat + 1 ≤ state.clock)
    (small : destination.toNat + size.toNat ≤ 33806089496) (aligned : destination.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "memzero") [destinationArgument,sizeArgument]) = (none,post) ∧
      ZeroBytePrefix post destination size.toNat ∧ state.clock ≤ post.clock + size.toNat + 1 ∧
      post.clock ≤ state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals ∧
      hashOccupiedCount size (hashOccupancyRead post destination) = 0 ∧
      ∀ watched : BitVec 64,
        (∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset) →
        (∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) →
        post.memory watched = state.memory watched := by
  obtain ⟨post,run,covered,cost,remaining,globals,postCode,addresses,endian,locals,empty⟩ :=
    evaluate_memzero_aligned_call state destinationArgument sizeArgument destination size arguments code budget
      small aligned wordDomain byteDomain
  refine ⟨post,run,covered,cost,remaining,globals,postCode,addresses,endian,locals,empty,?_⟩
  intro watched words bytes
  obtain ⟨framed,frameRun,memory,_,_,_,_,_,_,_⟩ :=
    evaluate_memzero_aligned_frame_call state destinationArgument sizeArgument destination size watched arguments code budget
      small aligned wordDomain words bytes byteDomain
  have equal : post = framed := congrArg Prod.snd (run.symm.trans frameRun)
  rw [equal]
  exact memory

#print axioms evaluate_memzero_aligned_call_with_frame
end InitECandidate.Runtime
