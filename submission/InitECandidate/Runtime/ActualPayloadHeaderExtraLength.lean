import InitECandidate.Runtime.ActualPayloadHeaderStrong
import InitECandidate.Runtime.MemzeroAlignedFrameCall
import InitECandidate.Runtime.KeccakFullCallWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- **An actual allocation preserves every watched word.**  The allocator changes only the heap
frontier global, never memory, so whatever cell was watched still holds its value. -/
theorem WatchWord.alloc {F : Type} {before after : PanSemStateFiniteExact 64 F}
    {address value : BitVec 64} (watch : WatchWord before address value)
    (memory : after.memory = before.memory) : WatchWord after address value :=
  watch.of_memory memory

#print axioms WatchWord.alloc

/-- **A watched word outside the zeroed interval survives the actual `memzero` call.**  The callee
writes exactly the `size` bytes it was asked to zero, so any cell strictly off the destination
interval -- including both the aligned byte cells and the unaligned padding tail -- is untouched. -/
theorem WatchWord.memzero {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (destinationArgument sizeArgument : ExpHOL 64) (destination size watched value : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [destinationArgument,sizeArgument] =
      some [.val (.word destination),.val (.word size)])
    (code : state.code = originalRuntimeCode) (budget : size.toNat + 1 ≤ state.clock)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (aligned : destination.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < size.toNat →
      state.memaddrs (destination + BitVec.ofNat 64 offset))
    (wordSeparate : ∀ offset : Nat, offset < size.toNat →
      watched ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat →
      watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat →
      state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (watch : WatchWord state watched value)
    (run : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "memzero") [destinationArgument,sizeArgument]) = (none,post)) :
    WatchWord post watched value := by
  obtain ⟨ending, finished, memory, _, _, _, _, _, _⟩ :=
    evaluate_memzero_aligned_frame_call state destinationArgument sizeArgument destination size watched
      arguments code budget small aligned wordDomain wordSeparate byteSeparate byteDomain
  rw [run] at finished
  cases finished
  unfold WatchWord at watch ⊢
  rw [memory]
  exact watch

#print axioms WatchWord.memzero

/-- **A watched word outside the keccak write windows survives the actual hash call.**  The call only
writes its state window, its pad window and its 32-byte output window, so a cell off all three -- such
as the loader's extra-length cell below the header -- keeps its value across the real call. -/
theorem WatchWord.keccak {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer pad source size output watched value : BitVec 64) (arguments : List (ExpHOL 64))
    (atState : state.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (args : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word source),.val (.word size),.val (.word output)])
    (small : size.toNat ≤ 134217712)
    (code : state.code = originalRuntimeCode) (budget : size.toNat * 20 + 43 ≤ state.clock)
    (outsideState : ¬ MWin pointer 200 watched) (outsidePad : ¬ MWin pad 136 watched)
    (outsideOutput : ¬ MWin output 32 watched)
    (watch : WatchWord state watched value)
    (run : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "keccak256") arguments) = (none,post)) :
    WatchWord post watched value := by
  have window := keccak_full_call_window state pointer pad source size output watched arguments
    atState atPad args small code budget outsideState outsidePad outsideOutput
  have memory := window.1
  rw [run] at memory
  unfold WatchWord at watch ⊢
  rw [memory]
  exact watch

#print axioms WatchWord.keccak

end InitECandidate.Runtime
