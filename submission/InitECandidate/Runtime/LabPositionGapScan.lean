import InitECandidate.Runtime.StackNativeLocalPrice
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget

/-- One-pass certificate: accumulated bytes belong to the preceding
instruction and following label padding. A new instruction starts a new gap. -/
def gapScan (bound accumulated : Nat) : List (LabLineHOL 64) → Bool
  | [] => decide (accumulated ≤ bound)
  | line :: rest =>
    if isLabelHOL line then gapScan bound (accumulated + lineLength line) rest
    else decide (accumulated ≤ bound) && gapScan bound (lineLength line) rest

def flatPosition (index position : Nat) : List (LabLineHOL 64) → Nat
  | [] => position
  | line :: rest =>
    if isLabelHOL line then flatPosition index (position + lineLength line) rest
    else if index = 0 then position
    else flatPosition (index - 1) (position + lineLength line) rest

theorem gapScan_mono {bound small large : Nat} {lines : List (LabLineHOL 64)}
    (le : small ≤ large) (checked : gapScan bound large lines = true) :
    gapScan bound small lines = true := by
  induction lines generalizing small large with
  | nil => simp only [gapScan, decide_eq_true_eq] at *; omega
  | cons line rest ih =>
    simp only [gapScan] at *
    split at checked
    · rename_i label
      simp only [label, Bool.false_eq_true, ↓reduceIte]
      exact ih (Nat.add_le_add_right le _) checked
    · rename_i label
      simp only [label, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at checked ⊢
      exact ⟨by omega, checked.2⟩

/-- The initial run of labels fits inside the current instruction's gap. -/
theorem gapScan_leading {bound accumulated position : Nat} {lines : List (LabLineHOL 64)}
    (checked : gapScan bound accumulated lines = true) :
    flatPosition 0 position lines + accumulated ≤ position + bound := by
  induction lines generalizing accumulated position with
  | nil => simp only [gapScan, decide_eq_true_eq] at checked; simp only [flatPosition]; omega
  | cons line rest ih =>
    simp only [gapScan, flatPosition] at *
    split at checked
    · rename_i label
      simp only [label, Bool.false_eq_true, ↓reduceIte]
      have h := ih checked (position := position + lineLength line)
      omega
    · rename_i label
      simp only [label, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
      omega

/-- The scan bounds every consecutive executed instruction position gap. -/
theorem gapScan_position {bound position index : Nat} {lines : List (LabLineHOL 64)}
    (checked : gapScan bound 0 lines = true) :
    flatPosition (index + 1) position lines - flatPosition index position lines ≤ bound := by
  induction lines generalizing position index with
  | nil => simp [flatPosition]
  | cons line rest ih =>
    simp only [gapScan] at checked
    simp only [flatPosition]
    split at checked
    · rename_i label
      simp only [label, Bool.false_eq_true, ↓reduceIte]
      exact ih (gapScan_mono (Nat.zero_le _) checked)
    · rename_i label
      simp only [label, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
      cases index with
      | zero =>
        simp only [Nat.zero_add, Nat.one_ne_zero, ↓reduceIte, Nat.sub_self]
        have h := gapScan_leading checked.2 (position := position + lineLength line)
        omega
      | succ index =>
        simp only [Nat.add_eq_zero_iff, Nat.succ_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel, Nat.add_sub_cancel_right]
        exact ih (gapScan_mono (Nat.zero_le _) checked.2)

theorem flatPosition_sections (index position : Nat) (code : LabProgHOL 64) :
    flatPosition index position (code.flatMap (fun sec => sec.lines)) = posVal index position code := by
  induction code generalizing index position with
  | nil => simp [flatPosition, posVal]
  | cons sec rest ih =>
    rcases sec with ⟨sid, lines⟩
    induction lines generalizing index position with
    | nil => simpa only [List.flatMap_cons, List.nil_append, posVal] using ih index position
    | cons line lines inner =>
      simp only [List.flatMap_cons, List.cons_append, flatPosition, posVal]
      split
      · exact inner index (position + lineLength line)
      · split
        · rfl
        · exact inner (index - 1) (position + lineLength line)

/-- A linear scan certificate discharges the finite maximum used by native prices. -/
theorem gapScan_encodedLineWords {bound : Nat} {code : LabProgHOL 64}
    (checked : gapScan bound 0 (code.flatMap (fun sec => sec.lines)) = true) :
    encodedLineWords code ≤ bound / 4 := by
  have gap (pc : Nat) : (posVal (pc + 1) 0 code - posVal pc 0 code) / 4 ≤ bound / 4 := by
    apply Nat.div_le_div_right
    simpa only [flatPosition_sections] using gapScan_position (position := 0) (index := pc) checked
  unfold encodedLineWords
  generalize numPcs code = count
  induction count with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    simp only [positionPrefixMax]
    exact max_le ih (gap count)

#print axioms flatPosition_sections
#print axioms gapScan_encodedLineWords
#print axioms gapScan_position
end InitECandidate.Runtime.StackToLab
