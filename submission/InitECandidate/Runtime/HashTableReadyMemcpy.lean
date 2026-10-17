import InitECandidate.Runtime.HashTableReadyIntervalFrame
import InitECandidate.Runtime.MemcpyAlignedFrameCall
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual aligned copy outside a live table preserves the complete shared
invariant, with its source-clock cost and caller-local restoration. -/
theorem HashTableReady.memcpy_outside {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (destinationArgument sourceArgument sizeArgument : ExpHOL 64) (destination source size : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (aligned : destination.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0) (budget : size.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (outside : destination.toNat + size.toNat ≤ table.toNat ∨
      orderPos.toNat + capacity.toNat * 8 ≤ destination.toNat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [destinationArgument,sourceArgument,sizeArgument] =
        some [.val (.word destination),.val (.word source),.val (.word size)]) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy")
        [destinationArgument,sourceArgument,sizeArgument]) = (none,post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
      state.clock ≤ post.clock + size.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals := by
  have separates : ∀ watched : BitVec 64, table.toNat ≤ watched.toNat →
      watched.toNat < orderPos.toNat + capacity.toNat * 8 →
      ∀ offset : Nat, offset < size.toNat →
      watched ≠ destination + BitVec.ofNat 64 offset ∧ watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset) := by
    intro watched lower upper
    apply memcpy_interval_separate destination size watched aligned small
    rcases outside with before | after
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have tableUpper : table.toNat < orderPos.toNat + capacity.toNat * 8 := by
    have hv := ready.live.arrays.headerValues
    have vu := ready.live.arrays.valuesBefore
    have uo := ready.live.arrays.usedBefore
    have oo := ready.live.arrays.orderBefore
    omega
  obtain ⟨post,run,_,cost,remaining,globals,code,domain,endian,locals⟩ :=
    evaluate_memcpy_aligned_frame_call state destinationArgument sourceArgument sizeArgument destination source size table
      small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain
      (fun offset inside => (separates table (by omega) tableUpper offset inside).1)
      (fun offset inside => (separates table (by omega) tableUpper offset inside).2) ready.live.arrays.code arguments
  have frame : ∀ watched : BitVec 64, table.toNat ≤ watched.toNat →
      watched.toNat < orderPos.toNat + capacity.toNat * 8 → post.memory watched = state.memory watched := by
    intro watched lower upper
    obtain ⟨checked,checkedRun,cell,_⟩ :=
      evaluate_memcpy_aligned_frame_call state destinationArgument sourceArgument sizeArgument destination source size watched
        small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain
        (fun offset inside => (separates watched lower upper offset inside).1)
        (fun offset inside => (separates watched lower upper offset inside).2) ready.live.arrays.code arguments
    have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
    rw [same]
    exact cell
  exact ⟨post,run,ready.interval_frame state post keyLength table pointer keys stride capacity used values order orderPos items bits
    frame globals code domain endian,cost,remaining,globals,code,domain,endian,locals⟩

#print axioms HashTableReady.memcpy_outside
end InitECandidate.Runtime
