import InitECandidate.Runtime.VersionedHashesBlobProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_versioned_hashes_blob_condition : versionedHashesBlobCondition =
    .cmp .less (.var .local (ofString "j")) (.var .local (ofString "nb")) := by
  simp only [versionedHashesBlobCondition,versionedHashesBlobLoop,versionedHashesScan,
    versionedHashesStep,versionedHashesLoop,versionedHashesAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def versionedHashesBlobRank {F : Type} (count : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "j") with
  | some (.val (.word index)) => count.toNat - index.toNat
  | _ => 0

/-- With the count below the signed boundary, the actual signed source guard
agrees with the natural-number rank used for termination. -/
theorem versioned_hashes_blob_rank_guard {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index count : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (countLocal : state.locals.lookup (ofString "nb") = some (.val (.word count)))
    (within : index.toNat ≤ count.toNat) (small : count.toNat < 2^63) :
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) versionedHashesBlobCondition =
      some (.val (.word (if versionedHashesBlobRank count state = 0 then (0 : BitVec 64) else 1))) := by
  by_cases inside : index.toNat < count.toNat
  · have positive : versionedHashesBlobRank count state ≠ 0 := by simp [versionedHashesBlobRank,indexLocal]; omega
    simp [source_versioned_hashes_blob_condition,evalHOLFinite,evalHOLExact,indexLocal,countLocal,
      Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess,inside,positive]
    omega
  · have zero : versionedHashesBlobRank count state = 0 := by simp [versionedHashesBlobRank,indexLocal]; omega
    simp [source_versioned_hashes_blob_condition,evalHOLFinite,evalHOLExact,indexLocal,countLocal,
      Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess,inside,zero]
    omega

/-- A real normal iteration decreases the rank without modular wraparound. -/
theorem versioned_hashes_blob_rank_decreases {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (inside : index.toNat < count.toNat)
    (run : evaluateHOLFiniteState state versionedHashesBlobStep = (none,post)) :
    post.locals.lookup (ofString "j") = some (.val (.word (index + 1))) ∧
      (index + 1).toNat ≤ count.toNat ∧ versionedHashesBlobRank count post < versionedHashesBlobRank count state := by
  have advanced := versioned_hashes_blob_step_adds_one state post index indexLocal run
  have add : (index + 1).toNat = index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change index.toNat + 1 < 2^64; omega)]
    rfl
  refine ⟨advanced,by omega,?_⟩
  simp only [versionedHashesBlobRank,indexLocal,advanced]
  rw [add]
  omega

#print axioms source_versioned_hashes_blob_condition
#print axioms versioned_hashes_blob_rank_guard
#print axioms versioned_hashes_blob_rank_decreases
end InitECandidate.Runtime
