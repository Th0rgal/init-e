import InitECandidate.Runtime.VersionedHashesBlobLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A count with its sign bit set makes the original signed comparison false
at the initial zero cursor, so it requires no loop-entry tick. -/
theorem versioned_hashes_blob_large_count_guard {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word 0)))
    (countLocal : state.locals.lookup (ofString "nb") = some (.val (.word count)))
    (large : 2^63 ≤ count.toNat) :
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      versionedHashesBlobCondition = some (.val (.word 0)) := by
  simp [source_versioned_hashes_blob_condition,evalHOLFinite,evalHOLExact,indexLocal,countLocal,
    Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess]
  omega

/-- The complete original inner loop has a bound for every 64-bit loaded
count; counts above the signed boundary exit immediately at j=0. -/
theorem evaluate_versioned_hashes_blob_entry_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count tx vh cursor : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word 0)))
    (countLocal : state.locals.lookup (ofString "nb") = some (.val (.word count)))
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (code : state.code = originalRuntimeCode)
    (budget : count.toNat * 130 ≤ state.clock) :
    let output := evaluateHOLFiniteState state versionedHashesBlobLoop
    state.clock ≤ output.2.clock + count.toNat * 130 ∧ output.2.clock ≤ state.clock ∧
      output.1 ≠ some .timeOut := by
  classical
  by_cases small : count.toNat < 2^63
  · let witness : VersionedHashesBlobLoopWitness state count tx vh :=
      ⟨⟨0,indexLocal,countLocal,by simp,small⟩,cursor,cursorLocal,txLocal,vhLocal,code⟩
    have rank : versionedHashesBlobRank count state = count.toNat := by
      simp [versionedHashesBlobRank,indexLocal]
    obtain ⟨result,post,run,total,remaining,noTimeout,_⟩ :=
      evaluate_versioned_hashes_blob_loop_bounded state count tx vh witness (by rw [rank]; exact budget)
    rw [run]
    exact ⟨by simpa only [rank] using total,remaining,noTimeout⟩
  · have guard := versioned_hashes_blob_large_count_guard state count indexLocal countLocal (by omega)
    rw [source_versioned_hashes_blob_loop,evaluateHOLFiniteState_while_total]
    rw [guard]
    simp

#print axioms versioned_hashes_blob_large_count_guard
#print axioms evaluate_versioned_hashes_blob_entry_bounded
end InitECandidate.Runtime
