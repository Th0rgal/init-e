import InitECandidate.Runtime.GasArithmetic

namespace InitECandidate.Runtime

/-- The three regular-gas funding cells of a frame: offsets 64, 184 and 192.
The invariant concerns their natural values, so word wrap cannot hide debt. -/
structure GasFunding where
  left : BitVec 64
  used : BitVec 64
  spilled : BitVec 64

def GasFunding.potential (frame : GasFunding) : Nat :=
  frame.left.toNat + frame.used.toNat + frame.spilled.toNat

/-- `charge_gas`: move funding from gas-left to regular-gas-used. -/
def GasFunding.charge (frame : GasFunding) (amount : BitVec 64) : GasFunding :=
  { frame with left := frame.left - amount, used := frame.used + amount }

/-- The spill branch of `charge_state_gas`: move gas-left to spill liability. -/
def GasFunding.spill (frame : GasFunding) (amount : BitVec 64) : GasFunding :=
  { frame with left := frame.left - amount, spilled := frame.spilled + amount }

/-- Both refunding a spill and repaying it after a successful child transfer
funding back to gas-left. The amount must not exceed the spill. -/
def GasFunding.repay (frame : GasFunding) (amount : BitVec 64) : GasFunding :=
  { frame with left := frame.left + amount, spilled := frame.spilled - amount }

/-- `frame_halt` consumes all remaining regular gas. -/
def GasFunding.halt (frame : GasFunding) : GasFunding :=
  { frame with left := 0, used := frame.used + frame.left }

theorem GasFunding.charge_potential (frame : GasFunding) (amount : BitVec 64)
    (budget : frame.potential ≤ 200000000) (enough : amount ≤ frame.left) :
    (frame.charge amount).potential = frame.potential := by
  have limit : frame.left.toNat + frame.used.toNat ≤ 200000000 := by
    unfold GasFunding.potential at budget
    omega
  simpa only [GasFunding.charge, GasFunding.potential] using
    congrArg (fun n => n + frame.spilled.toNat)
      (gasDebit_conservation frame.left frame.used amount enough
        (charge_noWrap frame.left frame.used amount enough limit))

theorem GasFunding.spill_potential (frame : GasFunding) (amount : BitVec 64)
    (budget : frame.potential ≤ 200000000) (enough : amount ≤ frame.left) :
    (frame.spill amount).potential = frame.potential := by
  have amountBound := BitVec.le_def.mp enough
  have noWrap : frame.spilled.toNat + amount.toNat < 2 ^ 64 := by
    unfold GasFunding.potential at budget
    omega
  simp only [GasFunding.spill, GasFunding.potential, BitVec.toNat_add,
    Nat.mod_eq_of_lt noWrap, gasDebit_toNat frame.left amount enough]
  omega

theorem GasFunding.repay_potential (frame : GasFunding) (amount : BitVec 64)
    (budget : frame.potential ≤ 200000000) (enough : amount ≤ frame.spilled) :
    (frame.repay amount).potential = frame.potential := by
  have amountBound := BitVec.le_def.mp enough
  have noWrap : frame.left.toNat + amount.toNat < 2 ^ 64 := by
    unfold GasFunding.potential at budget
    omega
  simp only [GasFunding.repay, GasFunding.potential, BitVec.toNat_add,
    Nat.mod_eq_of_lt noWrap, gasDebit_toNat frame.spilled amount enough]
  omega

theorem GasFunding.halt_potential (frame : GasFunding)
    (budget : frame.potential ≤ 200000000) :
    frame.halt.potential = frame.potential := by
  have noWrap : frame.used.toNat + frame.left.toNat < 2 ^ 64 := by
    unfold GasFunding.potential at budget
    omega
  change (0 : BitVec 64).toNat + (frame.used + frame.left).toNat + frame.spilled.toNat =
    frame.left.toNat + frame.used.toNat + frame.spilled.toNat
  have zero : (0 : BitVec 64).toNat = 0 := rfl
  rw [zero, BitVec.toNat_add, Nat.mod_eq_of_lt noWrap]
  omega

/-- Unsigned word minimum, matching the source helper. -/
def wordMin (left right : BitVec 64) : BitVec 64 :=
  if left.toNat < right.toNat then left else right

theorem wordMin_le_right (left right : BitVec 64) : wordMin left right ≤ right := by
  apply BitVec.le_def.mpr
  unfold wordMin
  split
  · omega
  · exact Nat.le_refl _

/-- A refund cannot mint regular funding: its repayment is capped by the
existing spill. This covers arbitrary word-sized refund requests. -/
theorem GasFunding.capped_refund (frame : GasFunding) (refund : BitVec 64)
    (budget : frame.potential ≤ 200000000) :
    (frame.repay (wordMin refund frame.spilled)).potential = frame.potential := by
  exact frame.repay_potential _ budget (wordMin_le_right _ _)

/-- Success-path child incorporation before spill repayment. -/
def GasFunding.merge (parent child : GasFunding) : GasFunding :=
  ⟨parent.left + child.left, parent.used + child.used, parent.spilled + child.spilled⟩

theorem GasFunding.merge_potential (parent child : GasFunding)
    (budget : parent.potential + child.potential ≤ 200000000) :
    (parent.merge child).potential = parent.potential + child.potential := by
  have leftBound : parent.left.toNat + child.left.toNat < 2 ^ 64 := by
    unfold GasFunding.potential at budget
    omega
  have usedBound : parent.used.toNat + child.used.toNat < 2 ^ 64 := by
    unfold GasFunding.potential at budget
    omega
  have spillBound : parent.spilled.toNat + child.spilled.toNat < 2 ^ 64 := by
    unfold GasFunding.potential at budget
    omega
  simp only [GasFunding.merge, GasFunding.potential, BitVec.toNat_add,
    Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt usedBound, Nat.mod_eq_of_lt spillBound]
  omega

/-- CALL first reserves forwarded gas through charge_gas, then removes the
child's allocation from the parent's used counter. Child allocation includes
any stipend, so proving `allocated ≤ used + forward` is essential. -/
def GasFunding.delegate (parent : GasFunding) (forward allocated : BitVec 64) : GasFunding :=
  { parent with left := parent.left - forward, used := (parent.used + forward) - allocated }

def childFunding (allocated : BitVec 64) : GasFunding := ⟨allocated, 0, 0⟩

theorem GasFunding.delegate_used (parent : GasFunding) (forward allocated : BitVec 64)
    (budget : parent.potential ≤ 200000000) (enough : forward ≤ parent.left)
    (allocation : allocated.toNat ≤ parent.used.toNat + forward.toNat) :
    (parent.delegate forward allocated).used.toNat =
      parent.used.toNat + forward.toNat - allocated.toNat := by
  have forwardBound := BitVec.le_def.mp enough
  have noWrap : parent.used.toNat + forward.toNat < 2 ^ 64 := by
    unfold GasFunding.potential at budget
    omega
  have allocationWord : allocated ≤ parent.used + forward := by
    apply BitVec.le_def.mpr
    simpa only [BitVec.toNat_add, Nat.mod_eq_of_lt noWrap] using allocation
  simp only [GasFunding.delegate, gasDebit_toNat _ _ allocationWord,
    BitVec.toNat_add, Nat.mod_eq_of_lt noWrap]

theorem GasFunding.delegate_potential (parent : GasFunding) (forward allocated : BitVec 64)
    (budget : parent.potential ≤ 200000000) (enough : forward ≤ parent.left)
    (allocation : allocated.toNat ≤ parent.used.toNat + forward.toNat) :
    (parent.delegate forward allocated).potential + (childFunding allocated).potential =
      parent.potential := by
  have used := parent.delegate_used forward allocated budget enough allocation
  have forwardBound := BitVec.le_def.mp enough
  have zero : (0 : BitVec 64).toNat = 0 := rfl
  unfold GasFunding.potential childFunding
  rw [used]
  simp only [GasFunding.delegate, gasDebit_toNat _ _ enough, zero, Nat.add_zero]
  omega

/-- The CALL value-transfer fee pays for its stipend: once this inequality is
established from the dispatch case, delegation cannot undo the opcode's net
positive regular-gas progress. This does not assume used is monotone between
individual stores inside CALL. -/
theorem call_delegation_progress (parent : GasFunding) (fee forward allocated : BitVec 64)
    (stipend : Nat)
    (budget : parent.potential ≤ 200000000) (feeEnough : fee ≤ parent.left)
    (forwardEnough : forward ≤ (parent.charge fee).left)
    (allocation : allocated.toNat = forward.toNat + stipend)
    (feePays : stipend + 1 ≤ fee.toNat) :
    parent.used.toNat + 1 ≤ ((parent.charge fee).delegate forward allocated).used.toNat := by
  have leftBound : parent.left.toNat + parent.used.toNat ≤ 200000000 := by
    unfold GasFunding.potential at budget
    omega
  have feeNoWrap := charge_noWrap parent.left parent.used fee feeEnough leftBound
  have chargedUsed : (parent.charge fee).used.toNat = parent.used.toNat + fee.toNat := by
    simp only [GasFunding.charge, BitVec.toNat_add, Nat.mod_eq_of_lt feeNoWrap]
  have chargedBudget : (parent.charge fee).potential ≤ 200000000 := by
    rwa [parent.charge_potential fee budget feeEnough]
  have canAllocate : allocated.toNat ≤ (parent.charge fee).used.toNat + forward.toNat := by
    rw [allocation, chargedUsed]
    omega
  rw [GasFunding.delegate_used _ _ _ chargedBudget forwardEnough canAllocate, chargedUsed, allocation]
  omega

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.GasFunding.capped_refund
#print axioms InitECandidate.Runtime.GasFunding.spill_potential

#print axioms InitECandidate.Runtime.call_delegation_progress
#print axioms InitECandidate.Runtime.GasFunding.delegate_potential
