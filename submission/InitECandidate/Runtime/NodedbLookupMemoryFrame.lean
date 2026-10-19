import InitECandidate.Runtime.NodedbLookupBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real database lookup keeps both memory and globals on every outcome. -/
theorem nodedb_lookup_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_nodedb_lookup) := by
  rw [source_nodedb_lookup_body]
  exact memoryFrame_decCall _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup htabGet_memoryFrame
    (memoryFrame_leaf _ (by
      simp only [nodedbLookupTail,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
      rfl))

#print axioms nodedb_lookup_memoryFrame
end InitECandidate.Runtime
