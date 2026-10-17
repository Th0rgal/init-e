import InitECandidate.Runtime.MptInsertExtensionAdvance
import InitECandidate.Runtime.CommonPrefixCallFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptInsertExtensionComparison : ProgHOL 64 :=
  match mptInsertKindDispatch with
  | .seq _ (.seq _ (.ite _ _ (.ite _ (.dec _ _ _ (.dec _ _ _ body)) _))) => body
  | _ => .skip

def mptInsertExtensionContinuation : ProgHOL 64 :=
  match mptInsertExtensionComparison with | .decCall _ _ _ _ body => body | _ => .skip

def mptInsertExtensionSplit : ProgHOL 64 :=
  match mptInsertExtensionContinuation with | .ite _ _ body => body | _ => .skip

def mptInsertPrefixArguments : List (ExpHOL 64) :=
  [.var .local (ofString "seg"),.var .local (ofString "sl"),
    .op .add [.var .local (ofString "key"),.var .local (ofString "level")],
    .op .sub [.var .local (ofString "klen"),.var .local (ofString "level")]]

theorem source_mptInsert_extension_comparison : mptInsertExtensionComparison =
    .decCall (ofString "pl") .one (ofString "common_prefix_length")
      mptInsertPrefixArguments mptInsertExtensionContinuation := by
  simp only [mptInsertExtensionComparison,mptInsertExtensionContinuation,mptInsertKindDispatch,mptInsertLoopStep,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_mptInsert_extension_continuation : mptInsertExtensionContinuation =
    .ite (.cmp .equal (.var .local (ofString "pl")) (.var .local (ofString "sl")))
      mptInsertExtensionAdvance mptInsertExtensionSplit := by
  simp only [mptInsertExtensionContinuation,mptInsertExtensionComparison,mptInsertExtensionAdvance,
    mptInsertExtensionSplit,mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Actual extension prefix comparison provides the remaining-key bound and
unchanged caller memory. A matched prefix takes the original advance path. -/
theorem evaluate_mptInsert_extension_comparison {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (segmentPointer segment key level length : BitVec 64)
    (segmentLocal : state.locals.lookup (ofString "seg") = some (.val (.word segmentPointer)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word segment)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (levelLocal : state.locals.lookup (ofString "level") = some (.val (.word level)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word length)))
    (bounded : level.toNat ≤ length.toNat) (code : state.code = originalRuntimeCode)
    (ticks : (wordMin segment (length - level)).toNat + 2 ≤ state.clock)
    (run : evaluateHOLFiniteState state mptInsertExtensionComparison = (none,post)) :
    ∃ (found : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      found.toNat ≤ segment.toNat ∧ level.toNat + found.toNat ≤ length.toNat ∧
      ready.locals = state.locals ∧ ready.memory = state.memory ∧ ready.globals = state.globals ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "pl") (.val (.word found)) ready)
        mptInsertExtensionContinuation = (none,output) ∧
      (found = segment → evaluateHOLFiniteState (setVarHOLFinite (ofString "pl") (.val (.word found)) ready)
        mptInsertExtensionAdvance = (none,output)) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "pl",state.locals.lookup (ofString "pl"))} := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      mptInsertPrefixArguments = some [.val (.word segmentPointer),.val (.word segment),.val (.word (key + level)),.val (.word (length - level))] := by
    simp [mptInsertPrefixArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,segmentLocal,sizeLocal,
      keyLocal,levelLocal,lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_mptInsert_extension_comparison] at run
  obtain ⟨found,ready,output,leftBound,rightBound,locals,memory,globals,tail,restored⟩ :=
    evaluate_commonPrefix_decCall_normal_frame state post (ofString "pl") mptInsertPrefixArguments
      mptInsertExtensionContinuation segmentPointer segment (key + level) (length - level) args code ticks run
  refine ⟨found,ready,output,leftBound,commonPrefix_result_fits_remaining_key level length found bounded rightBound,
    locals,memory,globals,tail,?_,restored⟩
  intro matched
  have atSize : (setVarHOLFinite (ofString "pl") (.val (.word found)) ready).locals.lookup (ofString "sl") =
      some (.val (.word segment)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "pl" ≠ ofString "sl" by decide] using sizeLocal
  have atPrefix : (setVarHOLFinite (ofString "pl") (.val (.word found)) ready).locals.lookup (ofString "pl") =
      some (.val (.word found)) := by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [source_mptInsert_extension_continuation,evaluateHOLFiniteState_ite] at tail
  have condition : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "pl") (.val (.word found)) ready).toExact
      (fun address => Classical.propDecidable ((setVarHOLFinite (ofString "pl") (.val (.word found)) ready).memaddrs address))
      (.cmp .equal (.var .local (ofString "pl")) (.var .local (ofString "sl"))) = some (.val (.word (1 : BitVec 64))) := by
    simp only [evalHOLExact,atPrefix,atSize]
    simp [matched,Compiler.Encoders.Asm.wordCmpHOL]
  rw [condition] at tail
  exact tail

#print axioms source_mptInsert_extension_comparison
#print axioms source_mptInsert_extension_continuation
#print axioms evaluate_mptInsert_extension_comparison
end InitECandidate.Runtime
