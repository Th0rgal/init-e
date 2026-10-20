import InitECandidate.Runtime.UniformWordDeclarationBound
import InitECandidate.Runtime.CommonPrefixOriginalBodyBound
import InitECandidate.Runtime.OriginalCommonPrefixCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A deliberately coarse uniform ceiling for the actual byte-prefix helper.
Its checked min result is a 64-bit word, and the real byte loop advances
without wrapping. Invalid locals or inaccessible input bytes reject. -/
theorem common_prefix_uniform_bounded :
 ProgBounded (sourceFunctionBody Guest.guestFn_common_prefix_length) (1+2^64) := by
 have minBound : FunBounded (ofString "min") 0 :=
  ⟨_,_,_,originalRuntimeCode_min_lookup,ProgBounded.straight _
   (by simp only [sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq];rfl)⟩
 intro F s code budget
 rw [source_commonPrefix_body]
 apply uniform_word_declaration_bounded s (ofString "n") (ofString "min") _ _ 0 (2^64) minBound code budget
 intro next length binding _ clock
 obtain ⟨result,post,run,spent,remaining,safe,_⟩:=
  evaluate_commonPrefix_after_min next length binding (by have := length.isLt;omega)
 unfold RunBounded
 rw [run]
 change next.clock≤post.clock+2^64 ∧ post.clock≤next.clock ∧ result≠some .timeOut
 exact ⟨by have := length.isLt;omega,remaining,safe⟩

theorem common_prefix_fun_bounded : FunBounded (ofString "common_prefix_length") (1+2^64) :=
 ⟨_,_,_,originalRuntimeCode_commonPrefix_lookup,common_prefix_uniform_bounded⟩

#print axioms common_prefix_uniform_bounded
#print axioms common_prefix_fun_bounded
end InitECandidate.Runtime
