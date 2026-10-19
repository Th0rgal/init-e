import InitECandidate.Runtime.NodedbLookupBodyBound
import InitECandidate.Runtime.RlpSliceInputPrefix
import InitECandidate.Runtime.NodedbSetValues
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original lookup tail dereferences the actual slice record selected by
hash-get. Its returned source and length are bounded by the original input. -/
theorem nodedb_lookup_tail_present_slice {F : Type} (s : PanSemStateFiniteExact 64 F)
    (present array index pointer length input inputLength : BitVec 64)
    (nonzero : present ≠ 0)
    (atResult : s.locals.lookup (ofString "r") = some
      (.rStruct [.val (.word present),.val (.word (array + index * 16))]))
    (slice : RlpSliceInputEntry s array index pointer length input inputLength) :
    evaluateHOLFiniteState s nodedbLookupTail =
      (some (.returned (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length)])),
        emptyLocalsHOLFinite s) ∧ length.toNat ≤ inputLength.toNat := by
  refine ⟨?_,slice.length_bound s array index pointer length input inputLength⟩
  have d0 := slice.readable.pointerDomain
  have d8 := slice.readable.lengthDomain
  have c0 := slice.readable.pointerCell
  have c8 := slice.readable.lengthCell
  unfold nodedbLookupTail sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_nodedb_lookup,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil]
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,evalListHOLExact,atResult,Compiler.Encoders.Asm.wordCmpHOL,nonzero,
    evaluateHOLFiniteState_skip,evaluateHOLFiniteState_return,wordOpHOL,wordOp,valueIsWord,valueWord,
    isWfShapeExactHOL,memLoadHOLExact,d0,d8,c0,c8,shapeOfHOLExact]
  have nz : present ≠ 0#64 := nonzero
  rw [if_neg nz]
  simp [evalHOLExact,evalListHOLExact,atResult,wordOpHOL,wordOp,valueIsWord,valueWord,
    isWfShapeExactHOL,memLoadHOLExact,d0,d8,c0,c8,shapeOfHOLExact]

/-- Registry membership and the actual slice prefix supply the record consumed
by the original tail; no source or length is guessed from the returned pointer. -/
theorem nodedb_lookup_tail_registry_slice {F : Type} (s : PanSemStateFiniteExact 64 F)
    (present record array total input inputLength : BitVec 64)
    (nonzero : present ≠ 0)
    (atResult : s.locals.lookup (ofString "r") = some (.rStruct [.val (.word present),.val (.word record)]))
    (member : record ∈ NodedbSliceTargets array total)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat) :
    ∃ pointer length : BitVec 64,
      evaluateHOLFiniteState s nodedbLookupTail =
        (some (.returned (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length)])),
          emptyLocalsHOLFinite s) ∧
      input.toNat ≤ pointer.toNat ∧ pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat ∧
      pointer.toNat + length.toNat < 2 ^ 64 ∧ length.toNat ≤ inputLength.toNat := by
  obtain ⟨index,inside,rfl⟩ := member
  obtain ⟨pointer,length,slice⟩ := slices index inside
  obtain ⟨run,bound⟩ := nodedb_lookup_tail_present_slice s present array index pointer length input inputLength
    nonzero atResult slice
  exact ⟨pointer,length,run,slice.startsWithin,slice.endsWithin,slice.noWrap,bound⟩

#print axioms nodedb_lookup_tail_present_slice
#print axioms nodedb_lookup_tail_registry_slice
end InitECandidate.Runtime
