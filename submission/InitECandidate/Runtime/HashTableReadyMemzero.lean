import InitECandidate.Runtime.MemzeroAlignedCombinedCall
import InitECandidate.Runtime.HashTableReadyIntervalFrame
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual occupancy zeroing preserves a disjoint ready table. -/
theorem HashTableReady.memzero_outside {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destinationArgument sizeArgument : ExpHOL 64) (destination size : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [destinationArgument,sizeArgument] =
        some [.val (.word destination),.val (.word size)])
    (code : state.code = originalRuntimeCode) (budget : size.toNat + 1 ≤ state.clock)
    (small : destination.toNat + size.toNat ≤ 33806089496) (aligned : destination.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (keyLength table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (outside : destination.toNat + size.toNat ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ destination.toNat) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memzero") [destinationArgument,sizeArgument]) = (none,post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
      hashOccupiedCount size (hashOccupancyRead post destination) = 0 ∧
      state.clock ≤ post.clock + size.toNat + 1 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals := by
  obtain ⟨post,run,_,cost,remaining,globals,postCode,domain,endian,locals,empty,frame⟩ :=
    evaluate_memzero_aligned_call_with_frame state destinationArgument sizeArgument destination size arguments code budget small aligned wordDomain byteDomain
  have preserved := ready.interval_frame state post keyLength table pointer keys stride capacity used values order orderPos items bits
    (by
      intro watched lower upper
      have separate := memcpy_interval_separate destination size watched aligned small
        (by rcases outside with before | after
            · exact Or.inr (by omega)
            · exact Or.inl (by omega))
      exact frame watched (fun offset inside => (separate offset inside).1) (fun offset inside => (separate offset inside).2))
    globals postCode domain endian
  exact ⟨post,run,preserved,empty,cost,remaining,globals,postCode,domain,endian,locals⟩

#print axioms HashTableReady.memzero_outside
end InitECandidate.Runtime
