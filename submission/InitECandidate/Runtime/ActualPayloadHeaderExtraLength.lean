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

/-- The byte-aligned cell of an address is never above it. -/
theorem panByteAlignHOL_toNat_le (address : BitVec 64) :
    (panByteAlignHOL address).toNat ≤ address.toNat := by
  simp only [panByteAlignHOL]
  have aligned : ((address.toNat / 2 ^ Nat.log2 (64 / 8)) * 2 ^ Nat.log2 (64 / 8)) ≤ address.toNat :=
    Nat.div_mul_le_self address.toNat _
  have small : ((address.toNat / 2 ^ Nat.log2 (64 / 8)) * 2 ^ Nat.log2 (64 / 8)) < 2^64 :=
    Nat.lt_of_le_of_lt aligned address.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  exact aligned

#print axioms panByteAlignHOL_toNat_le

/-- An aligned pointer is never above the byte cell of a later address. -/
theorem panByteAlignHOL_toNat_ge (pointer offset : BitVec 64)
    (aligned : pointer.toNat % 8 = 0) (cap : pointer.toNat ≤ 33806089496)
    (bound : offset.toNat < 248) :
    pointer.toNat ≤ (panByteAlignHOL (pointer + offset)).toNat := by
  simp only [panByteAlignHOL]
  have power : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
  rw [power]
  have sum : (pointer + offset).toNat = pointer.toNat + offset.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  have small : (pointer.toNat / 8) ≤ (pointer + offset).toNat / 8 :=
    Nat.div_le_div_right (by omega)
  have mono : (pointer.toNat / 8) * 8 ≤ ((pointer + offset).toNat / 8) * 8 :=
    Nat.mul_le_mul_right 8 small
  have exact' : (pointer.toNat / 8) * 8 = pointer.toNat := Nat.div_mul_cancel (by omega)
  have bound : ((pointer + offset).toNat / 8) * 8 < 2^64 := by
    have := Nat.div_mul_le_self (pointer + offset).toNat 8
    have := (pointer + offset).isLt
    omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  omega

#print axioms panByteAlignHOL_toNat_ge

/-- **The loader's extra-length cell sits strictly below the header.**  `pl + 136 ≤ pointer` puts
`pl + 24` before every word store and every byte-aligned cell of the header's memzero window. -/
theorem actual_payload_header_pl_cell_below (pl pointer : BitVec 64)
    (below : pl.toNat + 136 ≤ pointer.toNat) (cap : pointer.toNat ≤ 33806089496) :
    (pl + (24#64)).toNat + 112 ≤ pointer.toNat := by
  have twenty : (24#64).toNat = 24 := by decide
  have plAdd : (pl + (24#64)).toNat = pl.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by omega), twenty]
  omega

#print axioms actual_payload_header_pl_cell_below

/-- The extra-length cell is outside the header memzero window, word by word. -/
theorem actual_payload_header_pl_cell_word_separate (pl pointer : BitVec 64) (offset : Nat)
    (below : pl.toNat + 136 ≤ pointer.toNat) (cap : pointer.toNat ≤ 33806089496)
    (bound : offset < 248) : pl + (24#64) ≠ pointer + BitVec.ofNat 64 offset := by
  intro equal
  have left := actual_payload_header_pl_cell_below pl pointer below cap
  have right : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by
      have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have same : (pl + (24#64)).toNat = (pointer + BitVec.ofNat 64 offset).toNat := by rw [equal]
  rw [right] at same
  omega

#print axioms actual_payload_header_pl_cell_word_separate

/-- The extra-length cell is outside the header memzero window, byte cell by byte cell. -/
theorem actual_payload_header_pl_cell_byte_separate (pl pointer : BitVec 64) (offset : Nat)
    (below : pl.toNat + 136 ≤ pointer.toNat) (cap : pointer.toNat ≤ 33806089496)
    (aligned : pointer.toNat % 8 = 0) (bound : offset < 248) :
    pl + (24#64) ≠ panByteAlignHOL (pointer + BitVec.ofNat 64 offset) := by
  intro equal
  have left := actual_payload_header_pl_cell_below pl pointer below cap
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have above := panByteAlignHOL_toNat_ge pointer (BitVec.ofNat 64 offset) aligned cap (by rw [offsetNat]; exact bound)
  have same : (pl + (24#64)).toNat = (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)).toNat := by
    rw [equal]
  omega

#print axioms actual_payload_header_pl_cell_byte_separate

/-- **The actual memzero leaves the loader's extra-length cell alone.**  The header's window is
`[pointer, pointer + 248)` and `pl + 24` lies below `pointer`, so the watched extra length survives
the real call and the prefix facts and the zeroed window are still established. -/
theorem actual_payload_header_memzero_watched {F : Type}
    (state mid : PanSemStateFiniteExact 64 F) (pl raw pointer extraLen : BitVec 64)
    (facts : ActualPayloadHeaderBaseFacts state mid pl raw pointer (allocationEnd pointer (248#64)))
    (code : state.code = originalRuntimeCode)
    (guard : pointer.toNat + 248 ≤ 33806089496) (aligned : pointer.toNat % 8 = 0)
    (cap : pointer.toNat ≤ 33806089496)
    (wordDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 248 →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (below : pl.toNat + 136 ≤ pointer.toNat)
    (watch : WatchWord mid (pl + (24#64)) extraLen)
    (budget : 249 ≤ mid.clock) :
    Reaches mid (actualPayloadHeaderAt 3)
      (fun post => ActualPayloadHeaderBaseFacts state post pl raw pointer
          (allocationEnd pointer (248#64)) ∧ ZeroBytePrefix post pointer 248 ∧
        WatchWord post (pl + (24#64)) extraLen) 249 (actualPayloadHeaderAt 4) := by
  have sizeNat : (248#64).toNat = 248 := by decide
  have arguments : evalListHOLFinite mid
      (h := fun address => Classical.propDecidable (mid.memaddrs address))
      [.var .local (ofString "h"), .const (248#64)] =
      (some [ValueHOL.val (HolWordLab.word pointer), ValueHOL.val (HolWordLab.word (248#64))] :
        Option (List (ValueHOL 64))) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,facts.1.2.2.1]
  have codeMid : mid.code = originalRuntimeCode := by
    rw [facts.1.2.2.2.2.2]; exact code
  obtain ⟨post, run, zeroed, spent, kept, globals, postCode, domain, be, locals, occupied⟩ :=
    evaluate_memzero_aligned_call mid (.var .local (ofString "h")) (.const (248#64)) pointer (248#64)
      arguments codeMid (by omega) guard aligned
      (fun offset bound => by rw [facts.1.2.2.2.2.1]; exact wordDomain offset bound)
      (fun offset bound => by rw [facts.1.2.2.2.2.1]; exact byteDomain offset bound)
  have watched : WatchWord post (pl + (24#64)) extraLen :=
    WatchWord.memzero mid post (.var .local (ofString "h")) (.const (248#64)) pointer (248#64)
      (pl + (24#64)) extraLen arguments codeMid (by omega) guard aligned
      (fun offset bound => by rw [facts.1.2.2.2.2.1]; exact wordDomain offset bound)
      (fun offset bound => actual_payload_header_pl_cell_word_separate pl pointer offset below cap bound)
      (fun offset bound => actual_payload_header_pl_cell_byte_separate pl pointer offset below cap aligned bound)
      (fun offset bound => by rw [facts.1.2.2.2.2.1]; exact byteDomain offset bound)
      watch run
  rw [source_actual_payload_header_memzero]
  refine reaches_seq mid (ProgHOL.call (some (none,none)) (ofString "memzero")
    [.var .local (ofString "h"), .const (248#64)]) (actualPayloadHeaderAt 4) 249 _ ?_
  refine Or.inl ⟨post, ?_, by omega, by omega, run⟩
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩,zeroed,watched⟩
  · rw [locals]; exact facts.1.1
  · rw [locals]; exact facts.1.2.1
  · rw [locals]; exact facts.1.2.2.1
  · rw [globals]; exact facts.1.2.2.2.1
  · rw [domain]; exact facts.1.2.2.2.2.1
  · rw [postCode]; exact facts.1.2.2.2.2.2
  · intro name different
    rw [globals]
    exact facts.2 name different

#print axioms actual_payload_header_memzero_watched

/-- The extra-length cell is outside a keccak write window based at an aligned, higher address. -/
theorem actual_payload_header_pl_cell_not_mwin (pl base : BitVec 64) (width : Nat)
    (smallWidth : width ≤ 248)
    (below : pl.toNat + 136 ≤ base.toNat) (cap : base.toNat ≤ 33806089496)
    (aligned : base.toNat % 8 = 0) : ¬ MWin base width (pl + (24#64)) := by
  intro window
  obtain ⟨index, bound, separate | separate⟩ := window
  · exact actual_payload_header_pl_cell_word_separate pl base index below cap (by omega) separate
  · exact actual_payload_header_pl_cell_byte_separate pl base index below cap aligned (by omega)
      separate

#print axioms actual_payload_header_pl_cell_not_mwin

/-- **The actual keccak call leaves the loader's extra-length cell alone.**  The cell lies below the
header, hence outside the state window and the output window, and below the pad region, so the real
`keccak256(tmp, 1, oh)` preserves the watched extra length while still establishing the commit. -/
theorem actual_payload_header_keccak_watched {F : Type} (ref state : PanSemStateFiniteExact 64 F)
    (pl raw pointer heap oh tmp st pad extraLen : BitVec 64)
    (facts : ActualPayloadHeaderCommit ref state pl raw pointer heap oh tmp)
    (code : state.code = originalRuntimeCode)
    (atState : state.globals.lookup (ofString "keccak_st") = some (.val (.word st)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "tmp"), .const (1#64), .var .local (ofString "oh")] =
      some [.val (.word tmp),.val (.word (1#64)),.val (.word oh)])
    (ohAligned : oh.toNat % 8 = 0)
    (outsideState : ¬ MWin st 200 (pl + (24#64)))
    (outsidePad : ¬ MWin pad 136 (pl + (24#64)))
    (outsideOutput : ¬ MWin oh 32 (pl + (24#64)))
    (watch : WatchWord state (pl + (24#64)) extraLen)
    (ticks : 145 ≤ state.clock) :
    Reaches state (actualPayloadHeaderAt 9)
      (fun post => ActualPayloadHeaderCommit ref post pl raw pointer heap oh tmp ∧
        WatchWord post (pl + (24#64)) extraLen) 145 (actualPayloadHeaderAt 10) := by
  have one : (1#64 : BitVec 64).toNat = 1 := by decide
  have wide := runBounded_keccak_wide_full_call state st pad tmp (1#64) oh none
    [.var .local (ofString "tmp"), .const (1#64), .var .local (ofString "oh")]
    atState atPad args (by decide) ohAligned code (by omega)
  rw [source_actual_payload_header_keccak_shape]
  refine reaches_seq state actualPayloadHeaderKeccak (actualPayloadHeaderAt 10) 145 _ ?_
  unfold RunBounded at wide
  change state.clock ≤ (evaluateHOLFiniteState state actualPayloadHeaderKeccak).2.clock + 145 ∧
    (evaluateHOLFiniteState state actualPayloadHeaderKeccak).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 ≠ some .timeOut at wide
  by_cases normal : (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 = none
  · obtain ⟨post, run⟩ : ∃ post : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState state actualPayloadHeaderKeccak = (none, post) :=
      ⟨_, by rw [Prod.eq_iff_fst_eq_snd_eq]; exact ⟨normal,rfl⟩⟩
    refine Or.inl ⟨post, ?_, ?_, ?_, run⟩
    · exact ⟨actual_payload_header_commit_after_keccak ref state post pl raw pointer heap oh tmp
        facts code run,
        WatchWord.keccak state post st pad tmp (1#64) oh (pl + (24#64)) extraLen
          [.var .local (ofString "tmp"), .const (1#64), .var .local (ofString "oh")]
          atState atPad args (by rw [one]; decide) code (by rw [one]; omega)
          outsideState outsidePad outsideOutput watch run⟩
    · have spent := wide.1
      rw [run] at spent
      exact spent
    · have kept := wide.2.1
      rw [run] at kept
      exact kept
  · obtain ⟨x, run⟩ : ∃ result, (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 = some result := by
      cases placed : (evaluateHOLFiniteState state actualPayloadHeaderKeccak).1 with
      | none => exact absurd placed normal
      | some result => exact ⟨result,rfl⟩
    refine Or.inr ⟨x,run,?_,wide.1,wide.2.1,?_⟩
    · intro value returned
      have discard := evaluate_discard_call_no_return state (ofString "keccak256")
        [.var .local (ofString "tmp"), .const (1#64), .var .local (ofString "oh")] value
      exact discard (run.trans (congrArg some returned))
    · intro clock budget
      have different := wide.2.2
      rw [run] at different
      exact different (congrArg some budget)

#print axioms actual_payload_header_keccak_watched

end InitECandidate.Runtime
