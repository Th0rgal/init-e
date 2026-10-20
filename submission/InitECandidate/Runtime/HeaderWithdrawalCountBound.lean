import InitECandidate.Runtime.HeaderWithdrawalHeapChain
import InitECandidate.Runtime.TxFixedBytesArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The source's signed fixed-list-count limit is `2^63 - 1`, so a count the decoder accepted under
that limit is a machine-safe positive value. This is the arithmetic content of the actual
`ssz_fixed_list_count` guard (see `payload_withdrawals_suffix_returned`), exposed for the stored
payload field. -/
theorem wd_signed_count_bound (count withdrawals balance : BitVec 64)
    (_countVal : count = (balance - withdrawals) / 44)
    (within : ¬ (9223372036854775807 : BitVec 64) < count) :
    count.toNat < 2^63 := by
  have limVal : (9223372036854775807 : BitVec 64).toNat = 9223372036854775807 := by decide
  have bound := BitVec.le_def.mp (BitVec.not_lt.mp within)
  rw [limVal] at bound
  omega

/-- The withdrawal-count cell of the decoded payload struct: statement 43's load address `pl + 56`
holds the withdrawn-list count exported by the actual decoder. -/
theorem wd_slice_count_cell {F : Type} (post : PanSemStateFiniteExact 64 F)
    (array input wd count : BitVec 64)
    (entry : RlpSliceEntry post array (3#64) (input + wd) count) :
    post.memory (array + 56#64) = HolWordLab.word count ∧ post.memaddrs (array + 56#64) := by
  have h3 : (3#64 : BitVec 64) * (16#64) = 48#64 := by decide
  have h8 : (48#64 : BitVec 64) + (8#64) = 56#64 := by decide
  have cellAt : array + (3#64) * (16#64) + (8#64) = array + 56#64 := by
    rw [h3, BitVec.add_assoc, h8]
  refine ⟨?_,?_⟩
  · simpa only [cellAt] using entry.lengthCell
  · simpa only [cellAt] using entry.lengthDomain

/-- The withdrawals-array cell of the decoded payload struct: statement 43's earlier sibling read
`pl + 48` holds the array pointer `input + wd`, so the loop's `read = pl + 48` watches it. -/
theorem wd_slice_array_cell {F : Type} (post : PanSemStateFiniteExact 64 F)
    (array input wd count : BitVec 64)
    (entry : RlpSliceEntry post array (3#64) (input + wd) count) :
    post.memory (array + 48#64) = HolWordLab.word (input + wd) ∧ post.memaddrs (array + 48#64) := by
  have h3 : (3#64 : BitVec 64) * (16#64) = 48#64 := by decide
  have cellAt : array + (3#64) * (16#64) = array + 48#64 := by
    rw [h3]
  refine ⟨?_,?_⟩
  · simpa only [cellAt] using entry.pointerCell
  · simpa only [cellAt] using entry.pointerDomain

/-- Statement 46's window with every decoder-side input discharged: the withdrawal count bound comes
from the source's signed count limit, and both watched cells (`pl + 48` array pointer, `pl + 56` count)
come from the payload struct's actual slice entry. Only the heap geometry and the state bindings remain
as inputs. -/
theorem payloadHeader46_window_from_decoder {F : Type} (t : PanSemStateFiniteExact 64 F)
    (nwd pl slices heapBase w input wd size : BitVec 64) (withdrawals balance : BitVec 64)
    (entry : RlpSliceEntry t pl (3#64) (input + wd) nwd)
    (countVal : nwd = (balance - withdrawals) / 44)
    (within : ¬ (9223372036854775807 : BitVec 64) < nwd)
    (endEq : heapBase.toNat = slices.toNat + size.toNat)
    (sizeEq : size.toNat = 16 * nwd.toNat + 16)
    (alSlices : slices.toNat % 8 = 0) (alSize : size.toNat % 8 = 0)
    (cap : slices.toNat + 80 * nwd.toNat + 80 ≤ 33806089496)
    (atCounter : t.locals.lookup (ofString "i") = some (ValueHOL.val (HolWordLab.word 0#64)))
    (atNwd : t.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)))
    (atPl : t.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (freshE : t.locals.lookup (ofString "e") = none)
    (atSlices : t.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word slices)))
    (atHeap : t.globals.lookup (ofString "heap_ptr") = some (ValueHOL.val (HolWordLab.word heapBase)))
    (code : t.code = originalRuntimeCode)
    (slicesAbove : slices.toNat ≤ heapBase.toNat)
    (prologue : pl.toNat + 136 ≤ slices.toNat)
    (inHeader : w.toNat < pl.toNat + 136)
    (tail : (evaluateHOLFiniteState (evaluateHOLFiniteState t wdSliceLoop).2
        (actualPayloadHeaderAt 47)).2.memory w = (evaluateHOLFiniteState t wdSliceLoop).2.memory w) :
    (evaluateHOLFiniteState t (actualPayloadHeaderAt 46)).2.memory w = t.memory w := by
  have arrayCell := wd_slice_array_cell t pl input wd nwd entry
  have countBound := wd_signed_count_bound nwd withdrawals balance countVal within
  exact payloadHeader46_window_geometry_budget t nwd pl slices heapBase w (pl + 48#64) (input + wd) size
    rfl endEq sizeEq alSlices alSize cap atCounter atNwd atPl freshE atSlices atHeap code countBound
    slicesAbove (wd_read_below_arena pl slices (pl + 48#64) prologue rfl)
    (wd_watched_below_arena pl slices w prologue inHeader) arrayCell.2 arrayCell.1 tail

#print axioms payloadHeader46_window_from_decoder
/-- The statement 44 request size is the source expression `nwd * 16 + 16`, so its machine value is
`16 * nwd + 16` whenever the product does not wrap. -/
theorem wd_slice_size_value (nwd size : BitVec 64) (sizeVal : size = nwd * 16#64 + 16#64)
    (fit : nwd.toNat * 16 + 16 < 2^64) :
    size.toNat = 16 * nwd.toNat + 16 := by
  have s16 : (16#64 : BitVec 64).toNat = 16 := by decide
  have mulVal : (nwd * 16#64 : BitVec 64).toNat = nwd.toNat * 16 := by
    rw [BitVec.toNat_mul, s16, Nat.mod_eq_of_lt (by omega)]
  have addVal : (nwd * 16#64 + 16#64 : BitVec 64).toNat = nwd.toNat * 16 + 16 := by
    rw [BitVec.toNat_add, mulVal, s16, Nat.mod_eq_of_lt fit]
  rw [sizeVal, addVal]
  omega

/-- The state statement 46 starts from is the statement 43 entry state plus the two declarations:
`nwd` and `i := 0`. Memory, the address domain, the code and the globals are untouched, so the
decoded cells and the statement 44 arena survive into the loop. -/
theorem wd_slice_loop_entry_kit {F : Type} (s : PanSemStateFiniteExact 64 F) (nwd : BitVec 64) :
    let declared := setVarHOLFinite (ofString "nwd") (ValueHOL.val (HolWordLab.word nwd)) s
    let t := setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) declared
    t.locals.lookup (ofString "i") = some (ValueHOL.val (HolWordLab.word 0#64)) ∧
    t.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)) ∧
    t.locals.lookup (ofString "pl") = s.locals.lookup (ofString "pl") ∧
    t.locals.lookup (ofString "e") = s.locals.lookup (ofString "e") ∧
    t.memory = s.memory ∧ t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.globals = s.globals := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "nwd" by decide, show ofString "i" ≠ ofString "pl" by decide,
      show ofString "i" ≠ ofString "e" by decide, show ofString "nwd" ≠ ofString "pl" by decide,
      show ofString "nwd" ≠ ofString "e" by decide]

/-- Statement 46's window from the statement 43 entry state plus the two declaration bindings and the
statement 44 arena: the loop-entry state is `i := 0` on top of the allocated state, so the count bound,
both decoded cells, the address separation, the arena alignment and the range/limit facts all come from
the source facts. -/
theorem payloadHeader46_window_from_entry_state {F : Type}
    (s ready : PanSemStateFiniteExact 64 F)
    (nwd pl slices heapBase w input wd size : BitVec 64) (withdrawals balance : BitVec 64)
    (entry : RlpSliceEntry s pl (3#64) (input + wd) nwd)
    (countVal : nwd = (balance - withdrawals) / 44)
    (within : ¬ (9223372036854775807 : BitVec 64) < nwd)
    (sizeVal : size = nwd * 16#64 + 16#64)
    (sizeFit : nwd.toNat * 16 + 16 < 2^64)
    (alSlices : slices.toNat % 8 = 0) (alSize : size.toNat % 8 = 0)
    (cap : slices.toNat + 80 * nwd.toNat + 80 ≤ 33806089496)
    (readyLocals : ready.locals =
      (setVarHOLFinite (ofString "nwd") (ValueHOL.val (HolWordLab.word nwd)) s).locals)
    (readyMemory : ready.memory = s.memory) (readyMemaddrs : ready.memaddrs = s.memaddrs)
    (readyCode : ready.code = s.code)
    (readySlices : ready.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word slices)))
    (readyHeap : ready.globals.lookup (ofString "heap_ptr") =
      some (ValueHOL.val (HolWordLab.word heapBase)))
    (endEq : heapBase.toNat = slices.toNat + size.toNat)
    (atPl : s.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (freshE : s.locals.lookup (ofString "e") = none)
    (code : s.code = originalRuntimeCode)
    (slicesAbove : slices.toNat ≤ heapBase.toNat)
    (prologue : pl.toNat + 136 ≤ slices.toNat)
    (inHeader : w.toNat < pl.toNat + 136)
    (tail : (evaluateHOLFiniteState (evaluateHOLFiniteState
        (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready) wdSliceLoop).2
        (actualPayloadHeaderAt 47)).2.memory w =
      (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready)
        wdSliceLoop).2.memory w) :
    (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready)
      (actualPayloadHeaderAt 46)).2.memory w = s.memory w := by
  have ne_in : ofString "i" ≠ ofString "nwd" := by decide
  have ne_ip : ofString "i" ≠ ofString "pl" := by decide
  have ne_ie : ofString "i" ≠ ofString "e" := by decide
  have ne_np : ofString "nwd" ≠ ofString "pl" := by decide
  have ne_ne : ofString "nwd" ≠ ofString "e" := by decide
  have atCounter : (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready).locals.lookup
      (ofString "i") = some (ValueHOL.val (HolWordLab.word 0#64)) := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atNwd : (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready).locals.lookup
      (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)) := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne_in,readyLocals]
  have atPl : (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready).locals.lookup
      (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)) := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne_ip,readyLocals,ne_np,atPl]
  have atE : (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready).locals.lookup
      (ofString "e") = none := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne_ie,readyLocals,ne_ne,freshE]
  have entry' : RlpSliceEntry (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready)
      pl (3#64) (input + wd) nwd := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa [setVarHOLFinite,readyMemaddrs] using entry.pointerDomain
    · simpa [setVarHOLFinite,readyMemaddrs] using entry.lengthDomain
    · simpa [setVarHOLFinite,readyMemory] using entry.pointerCell
    · simpa [setVarHOLFinite,readyMemory] using entry.lengthCell
  have win := payloadHeader46_window_from_decoder
    (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready)
    nwd pl slices heapBase w input wd size withdrawals balance entry' countVal within endEq
    (wd_slice_size_value nwd size sizeVal sizeFit) alSlices alSize cap atCounter atNwd atPl atE
    (by simpa [setVarHOLFinite] using readySlices) (by simpa [setVarHOLFinite] using readyHeap)
    (by simpa [setVarHOLFinite,readyCode] using code) slicesAbove prologue inHeader tail
  simpa [setVarHOLFinite,readyMemory] using win

/-- The state statement 44's allocator call produces, recorded as one predicate: same locals,
memory, address domain and code as the declaration state, with the new array pointer and frontier. -/
def WdSliceArena {F : Type} (declared ready : PanSemStateFiniteExact 64 F)
    (slices size : BitVec 64) : Prop :=
  ready.locals = declared.locals ∧ ready.memory = declared.memory ∧
    ready.memaddrs = declared.memaddrs ∧ ready.code = declared.code ∧
    ready.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word slices)) ∧
    ready.globals.lookup (ofString "heap_ptr") =
      some (ValueHOL.val (HolWordLab.word (allocationEnd slices size)))

/-- Statement 46's window end to end from the statement 43 entry state: the actual statement 44
allocator call supplies the arena, the decoded count bound and both payload cells come from the
decoder, and the loop-entry state is `i := 0` on the allocated state. -/
theorem payloadHeader46_window_from_source {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nwd pl slices w input wd size : BitVec 64) (withdrawals balance : BitVec 64)
    (entry : RlpSliceEntry s pl (3#64) (input + wd) nwd)
    (countVal : nwd = (balance - withdrawals) / 44)
    (within : ¬ (9223372036854775807 : BitVec 64) < nwd)
    (sizeVal : size = nwd * 16#64 + 16#64)
    (sizeFit : nwd.toNat * 16 + 16 < 2^64)
    (alSlices : slices.toNat % 8 = 0) (alSize : size.toNat % 8 = 0)
    (cap : slices.toNat + 80 * nwd.toNat + 80 ≤ 33806089496)
    (atSlicesOld : s.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word slices)))
    (atHeapOld : s.globals.lookup (ofString "heap_ptr") =
      some (ValueHOL.val (HolWordLab.word slices)))
    (clock : (setVarHOLFinite (ofString "nwd") (ValueHOL.val (HolWordLab.word nwd)) s).clock ≠ 0)
    (allocArgs : evalListHOLFinite (setVarHOLFinite (ofString "nwd") (ValueHOL.val (HolWordLab.word nwd)) s)
      (h := fun a => Classical.propDecidable ((setVarHOLFinite (ofString "nwd")
        (ValueHOL.val (HolWordLab.word nwd)) s).memaddrs a))
      [.op .add [(.panop .mul [.var .local (ofString "nwd"), .const (16#64)]), .const (16#64)]] =
      some [.val (.word size)])
    (atPl : s.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (freshE : s.locals.lookup (ofString "e") = none)
    (code : s.code = originalRuntimeCode)
    (prologue : pl.toNat + 136 ≤ slices.toNat)
    (inHeader : w.toNat < pl.toNat + 136)
    (tailOk : ∀ ready, WdSliceArena (setVarHOLFinite (ofString "nwd")
        (ValueHOL.val (HolWordLab.word nwd)) s) ready slices size →
      (evaluateHOLFiniteState (evaluateHOLFiniteState
        (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready) wdSliceLoop).2
        (actualPayloadHeaderAt 47)).2.memory w =
      (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64))
        ready) wdSliceLoop).2.memory w) :
    ∃ ready, WdSliceArena (setVarHOLFinite (ofString "nwd") (ValueHOL.val (HolWordLab.word nwd)) s)
        ready slices size ∧
      (evaluateHOLFiniteState (evaluateHOLFiniteState
        (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready) wdSliceLoop).2
        (actualPayloadHeaderAt 47)).2.memory w =
      (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64))
        ready) wdSliceLoop).2.memory w ∧
      (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64))
        ready) (actualPayloadHeaderAt 46)).2.memory w = s.memory w := by
  have sizeEqV := wd_slice_size_value nwd size sizeVal sizeFit
  have bounded : slices.toNat + size.toNat ≤ 33806089496 := by rw [sizeEqV]; omega
  have alloc := wd_slices_alloc_entry
    (setVarHOLFinite (ofString "nwd") (ValueHOL.val (HolWordLab.word nwd)) s)
    nwd size slices sizeVal (wd_nwd_binding s nwd)
    (by simpa [setVarHOLFinite] using atSlicesOld) (by simpa [setVarHOLFinite] using atHeapOld)
    (by simpa [setVarHOLFinite] using code) clock allocArgs alSlices alSize bounded
  obtain ⟨ready, rest⟩ := alloc
  have run := rest.1
  have readyMemory := rest.2.1
  have readyMemaddrs := rest.2.2.1
  have readyLocals := rest.2.2.2.1
  have readyCode := rest.2.2.2.2.1
  have readySlices := rest.2.2.2.2.2.1
  have readyHeap := rest.2.2.2.2.2.2.1
  have endEq := rest.2.2.2.2.2.2.2.1
  have arena : WdSliceArena (setVarHOLFinite (ofString "nwd") (ValueHOL.val (HolWordLab.word nwd)) s)
      ready slices size :=
    ⟨readyLocals, by simpa [setVarHOLFinite] using readyMemory, by simpa [setVarHOLFinite] using readyMemaddrs,
      by simpa [setVarHOLFinite] using readyCode, readySlices, readyHeap⟩
  refine ⟨ready, arena, tailOk ready arena, ?_⟩
  exact payloadHeader46_window_from_entry_state s ready nwd pl slices (allocationEnd slices size) w input
    wd size withdrawals balance entry countVal within sizeVal sizeFit alSlices alSize cap readyLocals
    (by simpa [setVarHOLFinite] using readyMemory) (by simpa [setVarHOLFinite] using readyMemaddrs)
    (by simpa [setVarHOLFinite] using readyCode) readySlices readyHeap endEq atPl freshE code
    (by omega) prologue inHeader (tailOk ready arena)

#print axioms payloadHeader46_window_from_source
