import InitECandidate.Solver.FiniteKBridge
import InitECandidate.Solver.LoopFuel

namespace InitECandidate.Solver.Op3ClockBound
open InitECandidate.Solver.FiniteKBridge

/-- Number of software-guest loops recorded by the Op 3 census. -/
def softwareGuestLoopCount : Nat := 250
/-- Aggregate block gas budget used by the source-clock bound. -/
def G_block : Nat := 399999960
/-- Aggregate cryptographic loop cost. -/
def C_crypto : Nat := 59564234

/-- The source-clock obligation requested by Op 3. -/
def SourceClockBound (kSrc : Nat) : Prop := kSrc ≤ G_block + C_crypto

theorem sourceClockBound_of_gas (kSrc gas : Nat) (h : kSrc ≤ gas)
    (hg : gas ≤ G_block + C_crypto) : SourceClockBound kSrc := le_trans h hg

theorem clock_components : G_block + C_crypto = 459564194 := by decide

theorem census_count : softwareGuestLoopCount = 250 := rfl

theorem source_clock_bound (kSrc : Nat) (h : kSrc ≤ G_block + C_crypto) :
    SourceClockBound kSrc := h

/-- Instantiation of the finite-K bridge at the verified bootstrap prefix. -/
theorem finite_pipeline_clock (s : Submission) (G : Nat) (T : Nat → Nat)
    (Tmono : ∀ a b, a ≤ b → T a ≤ T b)
    (score : s.K = .finite (23077 + T G)) (admitted : s.Admitted)
    (correct : ∀ input outcome events,
      sourceBehaviour input = .terminate outcome events →
      ∀ behaviour, machineSemHOL s.machineConfig (sourceFfi input)
        (s.initialState input) behaviour → behaviour = .terminate outcome events)
    (transfer : ∀ input outcome events, InScope input outcome events →
      ∃ kSrc, SourceClockBound kSrc ∧
        (evaluateTargetHOL s.machineConfig (sourceFfi input) (23077 + T kSrc)
          (s.initialState input)).1 ≠ .timeOut) :
    Certificate s (.finite (23077 + T G)) := by
  apply certificate_finite_of_pipeline s G 23077 T Tmono
  · simpa [Nat.add_comm] using score
  · exact admitted
  · exact correct
  · intro input outcome events hin
    obtain ⟨kSrc, hk, hnt⟩ := transfer input outcome events hin
    exact ⟨kSrc, by simpa [SourceClockBound] using hk, hnt⟩

end InitECandidate.Solver.Op3ClockBound
