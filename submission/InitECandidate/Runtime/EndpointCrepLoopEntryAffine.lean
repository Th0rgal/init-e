import InitECandidate.Runtime.EndpointCrepLoopState
import InitECandidate.Runtime.BaselineCrepLoopEntryAffine
import InitECandidate.Runtime.BaselineCrepLoopEntry
import InitECandidate.Runtime.BaselineCrepLoopState
import InitECandidate.Runtime.BaselineCrepEntryFacts
import InitECandidate.Runtime.CrepWholeEntryAffine
import InitECandidate.Runtime.BaselineAffineFuelMono
import InitECandidate.Runtime.CrepAffine
import InitECandidate.Runtime.CrepEntryAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack

/-- Concrete generated code, entry lookup, compiler context and numeric code
bound are internal. Only the original word-memory premise and source run remain. -/
theorem endpoint_crep_loop_entry_bounded_affine {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (base capacity : BitVec 64)
    (words : noLabelsHOL (endpointFrontendState entry).memory
      (fun address => (endpointFrontendState entry).mdomain address = true))
    (fuel : Nat) (result : Option (CrepResultHOLExact 64))
    (post : CrepSemHOLState 64 Guest.HostMemory)
    (run : evalCrepSemHOLProgExact {endpointCrepState entry base capacity with clock := fuel}
      (.call none baselineCrepStart []) = (result,post))
    (good : result ≠ some .error) :
    ∃ extra, extra ≤ baselineCrepAffineExtraFuel fuel ∧ ∃ loopResult loopPost,
      LoopSemStateFiniteExact.evaluate (.call none (some firstLoopName) [] none)
        {endpointLoopState entry base capacity with clock := fuel + extra} = (loopResult,loopPost) ∧
      crepToLoopStateRelExact post loopPost ∧
      loopResult = Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop result := by
  apply crep_whole_entry_bounded_affine
    {endpointCrepState entry base capacity with clock := fuel}
    {endpointLoopState entry base capacity with clock := fuel}
    FrontendStages.pass3 baselineCrepStart firstLoopName
    Compiler.Encoders.RiscV.Target.riscvConfig.isa baselineCrepMainBody
    baselineCrepLimit baseline_crep_call_size ?_ ?_ ?_ ?_ baseline_crep_distinct
    ?_ ?_ rfl baseline_crep_main baseline_crep_functions_main result post run good
  · exact baseline_simplified_crep_bounded _ rfl
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact endpointCrepLoop_memory entry base capacity words
  · exact endpointCrepLoop_globals entry base capacity
  · rfl
  · change sptFromAList FrontendStages.pass4 = _
    rw [FrontendStages.pass4_eq]

#print axioms endpoint_crep_loop_entry_bounded_affine
end InitECandidate.Runtime
