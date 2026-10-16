import InitECandidate.Runtime.LabExtract

namespace InitECandidate.Runtime.LabToTarget
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem

/-- Labels are admitted structurally because fetching skips them. -/
def checkedLine : LabLineHOL 64 → Bool
  | .label _ _ _ => true
  | .asm (.asmi (.inst _)) _ _ => true
  | .asm (.asmi (.jumpReg _)) _ _ => true
  | .asm (.shareMem _ _ (.addr _ _)) _ _ => true
  | .labAsm .halt _ _ _ => true
  | .labAsm (.jump _) _ _ _ => true
  | .labAsm (.jumpCmp _ _ _ _) _ _ _ => true
  | .labAsm (.locValue _ _) _ _ _ => true
  | .labAsm (.callFFI _) _ _ _ => true
  | _ => false

def checkedSections (code : LabProgHOL 64) : Bool :=
  code.all (fun sec => sec.lines.all checkedLine)

theorem checkedSections_append (a b : LabProgHOL 64) :
    checkedSections (a ++ b) = (checkedSections a && checkedSections b) := by
  simp [checkedSections]

theorem checkedLine_supported (line : LabLineHOL 64)
    (checked : checkedLine line = true) (executable : isLabelHOL line = false) :
    SupportedLine line := by
  cases line with
  | label => simp [isLabelHOL] at executable
  | asm operation bytes n =>
    cases operation with
    | asmi instruction =>
      cases instruction <;> simp_all [checkedLine] <;> constructor
    | shareMem m r addr => cases addr; exact SupportedLine.shared _ _ _ _ _ _
    | _ => simp [checkedLine] at checked
  | labAsm operation w bytes n =>
    cases operation <;> simp_all [checkedLine] <;> constructor

/-- A kernel-checkable syntax pass suffices for every reachable fetch position. -/
theorem checkedSections_supported (code : LabProgHOL 64)
    (checked : checkedSections code = true) : SupportedCode code := by
  unfold SupportedCode
  induction code with
  | nil => intro pc line fetch; simp [asmFetchAux] at fetch
  | cons sec rest ih =>
    rcases sec with ⟨sid, lines⟩
    have checks : lines.all checkedLine = true ∧ checkedSections rest = true := by
      simpa [checkedSections] using checked
    have tail := ih checks.2
    clear ih checked
    induction lines with
    | nil => simpa only [asmFetchAux] using tail
    | cons first lines ihLines =>
      have parts : checkedLine first = true ∧ lines.all checkedLine = true := by
        simpa using checks.1
      have following := ihLines ⟨parts.2, checks.2⟩
      intro pc line fetch
      rw [asmFetchAux] at fetch
      split at fetch
      · exact following pc line fetch
      · rename_i nonlabel
        split at fetch
        · have eq := Option.some.inj fetch
          subst line
          exact checkedLine_supported first parts.1 (by simpa using nonlabel)
        · exact following (pc - 1) line fetch

#print axioms checkedSections_supported
end InitECandidate.Runtime.LabToTarget
