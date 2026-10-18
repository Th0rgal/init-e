import InitECandidate.Runtime.VersionedHashesIndexProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def versionedHashesCondition : ExpHOL 64 :=
  .cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))
def versionedHashesRank {F : Type} (count : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => count.toNat - index.toNat
  | _ => 0

theorem source_versioned_hashes_loop : versionedHashesLoop = .while versionedHashesCondition versionedHashesStep := by
  simp only [versionedHashesCondition,versionedHashesStep,versionedHashesLoop,versionedHashesAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- With the count below the signed boundary, the actual signed source guard
agrees with the natural-number rank used for termination. -/
theorem versioned_hashes_rank_guard {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index count : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (countLocal : state.locals.lookup (ofString "ntx") = some (.val (.word count)))
    (within : index.toNat ≤ count.toNat) (small : count.toNat < 2^63) :
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) versionedHashesCondition =
      some (.val (.word (if versionedHashesRank count state = 0 then (0 : BitVec 64) else 1))) := by
  by_cases inside : index.toNat < count.toNat
  · have positive : versionedHashesRank count state ≠ 0 := by simp [versionedHashesRank,indexLocal]; omega
    simp [versionedHashesCondition,evalHOLFinite,evalHOLExact,indexLocal,countLocal,
      Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess,inside,positive]
    omega
  · have zero : versionedHashesRank count state = 0 := by simp [versionedHashesRank,indexLocal]; omega
    simp [versionedHashesCondition,evalHOLFinite,evalHOLExact,indexLocal,countLocal,
      Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess,inside,zero]
    omega

/-- A real normal iteration decreases the rank without modular wraparound. -/
theorem versioned_hashes_rank_decreases {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (inside : index.toNat < count.toNat)
    (run : evaluateHOLFiniteState state versionedHashesStep = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      (index + 1).toNat ≤ count.toNat ∧ versionedHashesRank count post < versionedHashesRank count state := by
  have advanced := versioned_hashes_step_adds_one state post index indexLocal run
  have add : (index + 1).toNat = index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change index.toNat + 1 < 2^64; omega)]
    rfl
  refine ⟨advanced,by omega,?_⟩
  simp only [versionedHashesRank,indexLocal,advanced]
  rw [add]
  omega

#print axioms source_versioned_hashes_loop
#print axioms versioned_hashes_rank_guard
#print axioms versioned_hashes_rank_decreases
end InitECandidate.Runtime
