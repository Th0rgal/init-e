import InitECandidate.Runtime.ValidateHeadersStoredRootsRoomedLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- At the first loop's exit the runtime invariant still binds the caller's `hs` and `hashes`
locals, which is what the second phase's returned pair names. -/
theorem validate_headers_roomed_exit_locals {F : Type} (e : ValidateHeadersFirstEnvironment)
    (stop : PanSemStateFiniteExact 64 F)
    (roomed : ValidateHeadersStoredRootsRoomedInvariant e stop 0) :
    stop.locals.lookup (ofString "hs") = some (.val (.word e.hs)) ∧
      stop.locals.lookup (ofString "hashes") = some (.val (.word e.hashes)) := by
  obtain ⟨stored,_⟩ := roomed
  obtain ⟨pointer,_⟩ := stored
  obtain ⟨_,_,_,_,_,hsBind,hashesBind,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := pointer.1
  exact ⟨hsBind,hashesBind⟩

#print axioms validate_headers_roomed_exit_locals
end InitECandidate.Runtime
