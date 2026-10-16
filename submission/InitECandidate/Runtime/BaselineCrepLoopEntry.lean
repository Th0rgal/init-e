import InitECandidate.Runtime.BaselineCrepLoopState
import InitECandidate.Runtime.BaselineCrepEntryFacts
import InitECandidate.Runtime.CrepWholeEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack

noncomputable def baselineCrepExtraFuel (fuel : Nat) : Nat :=
  workCeiling baselineCrepLimit fuel
    (sizeOf (CrepProgHOL.call none baselineCrepStart [] : CrepProgHOL 64))

/-- Concrete generated code, entry lookup, compiler context and numeric code
bound are internal. Only the original word-memory premise and source run remain. -/
theorem baseline_crep_loop_entry_bounded {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (base capacity : BitVec 64)
    (words : noLabelsHOL (entryFrontendState entry).memory
      (fun address => (entryFrontendState entry).mdomain address = true))
    (fuel : Nat) (result : Option (CrepResultHOLExact 64))
    (post : CrepSemHOLState 64 Guest.HostMemory)
    (run : evalCrepSemHOLProgExact {entryCrepState entry base capacity with clock := fuel}
      (.call none baselineCrepStart []) = (result,post))
    (good : result ≠ some .error) :
    ∃ extra, extra ≤ baselineCrepExtraFuel fuel ∧ ∃ loopResult loopPost,
      LoopSemStateFiniteExact.evaluate (.call none (some firstLoopName) [] none)
        {entryLoopState entry base capacity with clock := fuel + extra} = (loopResult,loopPost) ∧
      crepToLoopStateRelExact post loopPost ∧
      loopResult = Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop result := by
  apply crep_whole_entry_bounded
    {entryCrepState entry base capacity with clock := fuel}
    {entryLoopState entry base capacity with clock := fuel}
    FrontendStages.pass3 baselineCrepStart firstLoopName
    Compiler.Encoders.RiscV.Target.riscvConfig.isa baselineCrepMainBody
    baselineCrepLimit baseline_crep_call_size ?_ ?_ ?_ ?_ baseline_crep_distinct
    ?_ ?_ rfl baseline_crep_main baseline_crep_functions_main result post run good
  · exact baseline_simplified_crep_bounded _ rfl
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact entryCrepLoop_memory entry base capacity words
  · exact entryCrepLoop_globals entry base capacity
  · rfl
  · change sptFromAList FrontendStages.pass4 = _
    rw [FrontendStages.pass4_eq]

#print axioms baseline_crep_loop_entry_bounded
end InitECandidate.Runtime
