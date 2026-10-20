import InitECandidate.Runtime.HeaderWithdrawalLoopBody
import InitECandidate.Runtime.MptReadFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The encoder argument of iteration `k` reads the 32-byte slice record at `pl + 48 + 44 * i`. -/
theorem wd_slice_args {F : Type} (s : PanSemStateFiniteExact 64 F) (I0 pl X : BitVec 64) (k : Nat)
    (atPl : s.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (atI : s.locals.lookup (ofString "i") =
      some (ValueHOL.val (HolWordLab.word (I0 + BitVec.ofNat 64 k))))
    (addrOk : s.memaddrs (pl + 48#64))
    (mem : s.memory (pl + 48#64) = HolWordLab.word X) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
        .panop .mul [.var .local (ofString "i"), .const (44#64)]]] =
      some [ValueHOL.val (HolWordLab.word (X + (I0 + BitVec.ofNat 64 k) * 44#64))] := by
  rw [evalListHOLFinite_eq_toExact]
  simp [evalListHOLExact,evalHOLExact,panOpHOL,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,
    atPl,atI,addrOk,mem]

/-- Invariant of the payload-header slice loop: the counter is the initial index plus the number of
completed iterations, the heap pointer is the matching heap word, and both watched cells are still
the entry values. -/
def wdSliceInv {F : Type} (t : PanSemStateFiniteExact 64 F)
    (I0 nwd pl slices w read : BitVec 64) (H : Nat → BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ k : Nat, I0.toNat + k ≤ nwd.toNat ∧
    s.locals.lookup (ofString "i") =
      some (ValueHOL.val (HolWordLab.word (I0 + BitVec.ofNat 64 k))) ∧
    s.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)) ∧
    s.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)) ∧
    s.locals.lookup (ofString "e") = none ∧
    s.globals.lookup (ofString "wd_rlp_slices") = some (ValueHOL.val (HolWordLab.word slices)) ∧
    s.globals.lookup (ofString "heap_ptr") = some (ValueHOL.val (HolWordLab.word (H k))) ∧
    s.code = originalRuntimeCode ∧
    s.memaddrs read ∧
    s.memory w = t.memory w ∧
    s.memory read = t.memory read

/-- The withdrawal slice loop keeps the watched cell at every fuel. -/
theorem wdSliceLoop_window {F : Type} (t : PanSemStateFiniteExact 64 F)
    (I0 nwd pl slices heapBase w read X : BitVec 64) (H : Nat → BitVec 64)
    (readEq : read = pl + 48#64)
    (atCounter : t.locals.lookup (ofString "i") = some (ValueHOL.val (HolWordLab.word I0)))
    (atNwd : t.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)))
    (atPl : t.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (freshE : t.locals.lookup (ofString "e") = none)
    (atSlices : t.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word slices)))
    (atHeap : t.globals.lookup (ofString "heap_ptr") = some (ValueHOL.val (HolWordLab.word heapBase)))
    (code : t.code = originalRuntimeCode)
    (heap0 : H 0 = heapBase)
    (heapStep : ∀ j, H (j + 1) = allocationEnd (H j) 64)
    (initialLe : I0.toNat ≤ nwd.toNat)
    (smallNwd : nwd.toNat < 2^63)
    (bounds : ∀ j, j ≤ nwd.toNat → (H j).toNat + 64 < 2^64)
    (outW : ∀ j, j ≤ nwd.toNat → ¬ MWin (H j) 64 w)
    (outR : ∀ j, j ≤ nwd.toNat → ¬ MWin (H j) 64 read)
    (addrRead : t.memaddrs read)
    (sliceW : ∀ j, j ≤ nwd.toNat →
      w ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 ∧
      w ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 + 8#64)
    (sliceR : ∀ j, j ≤ nwd.toNat →
      read ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 ∧
      read ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 + 8#64)
    (noControl : ∀ s : PanSemStateFiniteExact 64 F,
      wdSliceInv t I0 nwd pl slices w read H s →
      (evaluateHOLFiniteState (decClockHOLFinite s) wdSliceLoopBody).1 ≠ some .continue ∧
      (evaluateHOLFiniteState (decClockHOLFinite s) wdSliceLoopBody).1 ≠ some .break)
    (memRead : t.memory read = HolWordLab.word X) :
    (evaluateHOLFiniteState t wdSliceLoop).2.memory w = t.memory w := by
  have inv0 : wdSliceInv t I0 nwd pl slices w read H t := by
    refine ⟨0, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using atCounter
    · simpa using atNwd
    · simpa using atPl
    · simpa using freshE
    · simpa using atSlices
    · simpa [heap0] using atHeap
    · simpa using code
    · simpa using addrRead
    · rfl
    · rfl
  apply (evaluate_while_watch wdSliceLoopCondition wdSliceLoopBody w
    (wdSliceInv t I0 nwd pl slices w read H) ?_ t inv0).1
  intro s inv v hv nz
  have invKeep := inv
  obtain ⟨k, hk, atI, atNwd', atPl', freshE', atSlices', atHeap', code', addr', memW, memR⟩ := inv
  have hk' : k ≤ nwd.toNat := by omega
  let entered := decClockHOLFinite s
  have eI : entered.locals.lookup (ofString "i") =
      some (ValueHOL.val (HolWordLab.word (I0 + BitVec.ofNat 64 k))) := by
    simpa [entered,decClockHOLFinite] using atI
  have eSlices : entered.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word slices)) := by
    simpa [entered,decClockHOLFinite] using atSlices'
  have eHeap : entered.globals.lookup (ofString "heap_ptr") =
      some (ValueHOL.val (HolWordLab.word (H k))) := by
    simpa [entered,decClockHOLFinite] using atHeap'
  have eCode : entered.code = originalRuntimeCode := by
    simpa [entered,decClockHOLFinite] using code'
  have eAddr : entered.memaddrs read := by
    simpa [entered,decClockHOLFinite] using addr'
  have eMem : entered.memory read = HolWordLab.word X := by
    rw [show entered.memory read = s.memory read from by simp [entered,decClockHOLFinite]]
    rw [memR, memRead]
  have args : evalListHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
      [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
        .panop .mul [.var .local (ofString "i"), .const (44#64)]]] =
      some [ValueHOL.val (HolWordLab.word (X + (I0 + BitVec.ofNat 64 k) * 44#64))] := by
    apply wd_slice_args entered I0 pl X k
    · simpa [entered,decClockHOLFinite] using atPl'
    · simpa [entered,decClockHOLFinite] using atI
    · simpa [readEq] using eAddr
    · simpa [readEq] using eMem
  have windowW : (evaluateHOLFiniteState entered wdSliceLoopBody).2.memory w = s.memory w := by
    rw [show s.memory w = entered.memory w from by simp [entered,decClockHOLFinite]]
    apply wd_slice_step_window entered slices (I0 + BitVec.ofNat 64 k)
      (X + (I0 + BitVec.ofNat 64 k) * 44#64) (H k) w
    · exact eI
    · exact eSlices
    · exact eHeap
    · exact eCode
    · have := bounds k hk'
      simpa using this
    · exact outW k hk'
    · exact (sliceW k hk').1
    · simpa only [BitVec.add_assoc] using (sliceW k hk').2
    · exact args
  have windowR : (evaluateHOLFiniteState entered wdSliceLoopBody).2.memory read = s.memory read := by
    rw [show s.memory read = entered.memory read from by simp [entered,decClockHOLFinite]]
    apply wd_slice_step_window entered slices (I0 + BitVec.ofNat 64 k)
      (X + (I0 + BitVec.ofNat 64 k) * 44#64) (H k) read
    · exact eI
    · exact eSlices
    · exact eHeap
    · exact eCode
    · have := bounds k hk'
      simpa using this
    · exact outR k hk'
    · exact (sliceR k hk').1
    · simpa only [BitVec.add_assoc] using (sliceR k hk').2
    · exact args
  have noWrap : I0.toNat + k < 2^64 := by omega
  have toNatEq : (I0 + BitVec.ofNat 64 k).toNat = I0.toNat + k := by
    rw [BitVec.toNat_add]
    have off : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [off, Nat.mod_eq_of_lt noWrap]
  have condTrue : (I0 + BitVec.ofNat 64 k).toNat < nwd.toNat := by
    have smallI : (I0 + BitVec.ofNat 64 k).toNat < 2^63 := by omega
    exact (cond_less_small s (I0 + BitVec.ofNat 64 k) nwd v atI atNwd' smallI smallNwd hv).mp nz
  have succI : (I0 + BitVec.ofNat 64 k) + 1#64 = I0 + BitVec.ofNat 64 (k + 1) := by
    have : (BitVec.ofNat 64 (k + 1) : BitVec 64) = BitVec.ofNat 64 k + 1#64 := by
      rw [BitVec.ofNat_add]
    rw [this, BitVec.add_assoc]
  refine ⟨windowW, ?_⟩
  intro outcome
  rcases outcome with normal | hcont | hbreak
  · have out := wd_slice_step_outcome entered (X + (I0 + BitVec.ofNat 64 k) * 44#64) eCode args normal
    obtain ⟨first,second,st,bodyRun,shapeOk⟩ := out
    have succ := wd_slice_step_successor entered (I0 + BitVec.ofNat 64 k) nwd pl slices (H k)
      (X + (I0 + BitVec.ofNat 64 k) * 44#64) first second st
      eI (by simpa [entered,decClockHOLFinite] using atNwd')
      (by simpa [entered,decClockHOLFinite] using atPl')
      (by simpa [entered,decClockHOLFinite] using freshE')
      eSlices eHeap eCode args bodyRun shapeOk normal
    have hl := succ.1
    have hn := succ.2.1
    have hp := succ.2.2.1
    have he := succ.2.2.2.1
    have hs := succ.2.2.2.2.1
    have hh := succ.2.2.2.2.2
    have hcode : (evaluateHOLFiniteState entered wdSliceLoopBody).2.code = originalRuntimeCode := by
      have metadata := evaluateHOLFiniteState_metadata entered wdSliceLoopBody
      rw [metadata.1]
      exact eCode
    refine ⟨k + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [succI] using hl
    · exact hn
    · exact hp
    · exact he
    · exact hs
    · simpa only [heapStep] using hh
    · exact hcode
    · have metadata := evaluateHOLFiniteState_metadata entered wdSliceLoopBody
      rw [metadata.2.1]
      exact eAddr
    · rw [windowW]
      simpa [entered,decClockHOLFinite] using memW
    · rw [windowR]
      simpa [entered,decClockHOLFinite] using memR
  · exact absurd hcont (noControl s invKeep).1
  · exact absurd hbreak (noControl s invKeep).2

#print axioms wd_slice_args
#print axioms wdSliceLoop_window
end InitECandidate.Runtime
