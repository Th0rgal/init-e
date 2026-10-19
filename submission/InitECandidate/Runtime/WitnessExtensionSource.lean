import InitECandidate.Runtime.DecodeWitnessNodeLoopSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def witnessUnwindNonempty : ProgHOL 64 :=
  match decodeWitnessNodeUnwindMode with | .ite _ _ body => body | _ => .skip

def witnessUnwindExtension : ProgHOL 64 :=
  match witnessUnwindNonempty with
  | .dec _ _ _ (.seq _ (.ite _ body _)) => body
  | _ => .skip

def witnessExtensionKindScope : ProgHOL 64 :=
  match witnessUnwindExtension with | .seq _ body => body | _ => .skip

def witnessExtensionConstructor : ProgHOL 64 :=
  match witnessExtensionKindScope with | .dec _ _ _ (.seq _ body) => body | _ => .skip

def witnessExtensionStores : ProgHOL 64 :=
  match witnessExtensionConstructor with | .decCall _ _ _ _ body => body | _ => .skip

def witnessUnwindBranch : ProgHOL 64 :=
  match witnessUnwindNonempty with
  | .dec _ _ _ (.seq _ (.ite _ _ body)) => body
  | _ => .skip

def witnessUnwindHashStore : ProgHOL 64 :=
  match witnessUnwindNonempty with | .dec _ _ _ (.seq body _) => body | _ => .skip

theorem source_witness_unwind_dispatch : decodeWitnessNodeUnwindMode =
  .ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
    (.assign .local (ofString "go") (.const 0)) witnessUnwindNonempty := by
  simp only [witnessUnwindNonempty,decodeWitnessNodeUnwindMode,decodeWitnessNodeIteration,
    decodeWitnessNodeBodyAt,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_unwind_nonempty : witnessUnwindNonempty =
  .dec (ofString "hash") .one (.load .one (.op .add [.var .local (ofString "top"),.const 80]))
    (.seq witnessUnwindHashStore
      (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "top"),.const 8])) (.const 1))
        witnessUnwindExtension witnessUnwindBranch)) := by
  simp only [witnessUnwindHashStore,witnessUnwindBranch,witnessUnwindExtension,witnessUnwindNonempty,
    decodeWitnessNodeUnwindMode,decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_unwind_hash_store : witnessUnwindHashStore =
  .ite (.op .and [.cmp .notEqual (.const 0) (.cmp .notEqual (.var .local (ofString "hash")) (.const 0)),
    .cmp .notEqual (.const 0) (.cmp .notEqual (.var .local (ofString "result")) (.const 0))])
    (.store (.op .add [.var .local (ofString "result"),.const 24]) (.var .local (ofString "hash"))) .skip := by
  simp only [witnessUnwindHashStore,witnessUnwindNonempty,decodeWitnessNodeUnwindMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def witnessExtensionArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "top"),.const 64]),
   .load .one (.op .add [.var .local (ofString "top"),.const 72]),.var .local (ofString "result")]

def witnessExtensionKindCheck : ExpHOL 64 :=
  .op .and [.cmp .notEqual (.const 0) (.cmp .notEqual (.var .local (ofString "ck")) (.const 3)),
    .cmp .notEqual (.const 0) (.cmp .notEqual (.var .local (ofString "ck")) (.const 0))]

theorem source_witness_extension : witnessUnwindExtension =
  .seq (.ite (.cmp .equal (.var .local (ofString "result")) (.const 0))
    (.call (some (none,none)) (ofString "mpt_fail") [.const 8]) .skip) witnessExtensionKindScope := by
  simp only [witnessUnwindExtension,witnessExtensionKindScope,witnessUnwindNonempty,
    decodeWitnessNodeUnwindMode,decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_extension_kind_scope : witnessExtensionKindScope =
  .dec (ofString "ck") .one (.load .one (.op .add [.var .local (ofString "result"),.const 0]))
    (.seq (.ite witnessExtensionKindCheck
      (.call (some (none,none)) (ofString "mpt_fail") [.const 8]) .skip) witnessExtensionConstructor) := by
  simp only [witnessExtensionConstructor,witnessExtensionKindScope,witnessUnwindExtension,
    witnessUnwindNonempty,witnessExtensionKindCheck,decodeWitnessNodeUnwindMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_extension_constructor : witnessExtensionConstructor =
  .decCall (ofString "ex") .one (ofString "node_new_ext") witnessExtensionArguments witnessExtensionStores := by
  simp only [witnessExtensionStores,witnessExtensionConstructor,witnessExtensionKindScope,
    witnessUnwindExtension,witnessUnwindNonempty,witnessExtensionArguments,decodeWitnessNodeUnwindMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_extension_stores : witnessExtensionStores =
  .seq (.store (.op .add [.var .local (ofString "ex"),.const 8])
    (.load .one (.op .add [.var .local (ofString "top"),.const 48])))
  (.seq (.store (.op .add [.var .local (ofString "ex"),.const 16])
    (.load .one (.op .add [.var .local (ofString "top"),.const 56])))
  (.seq (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"),.const 0])))
    (.assign .local (ofString "result") (.var .local (ofString "ex"))))) := by
  simp only [witnessExtensionStores,witnessExtensionConstructor,witnessExtensionKindScope,
    witnessUnwindExtension,witnessUnwindNonempty,decodeWitnessNodeUnwindMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_witness_unwind_dispatch
#print axioms source_witness_unwind_nonempty
#print axioms source_witness_unwind_hash_store
#print axioms source_witness_extension
#print axioms source_witness_extension_kind_scope
#print axioms source_witness_extension_constructor
#print axioms source_witness_extension_stores
end InitECandidate.Runtime
