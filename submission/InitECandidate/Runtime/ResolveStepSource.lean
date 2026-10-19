import InitECandidate.Runtime.StateInitJournalSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def resolveStepAt (n : Nat) : ProgHOL 64 := stateInitSpineDrop n (sourceFunctionBody Guest.guestFn__resolve_step)
def resolveStepParseCall : ProgHOL 64 := match resolveStepAt 2 with | .seq call _ => call | _ => .skip
def resolveStepStringBranch : ProgHOL 64 := match resolveStepAt 3 with | .seq (.ite _ body _) _ => body | _ => .skip
def resolveStepLookup : ProgHOL 64 := match resolveStepStringBranch with | .seq _ (.seq _ body) => body | _ => .skip
def resolveStepLookupTail : ProgHOL 64 := match resolveStepLookup with | .decCall _ _ _ _ body => body | _ => .skip
def resolveStepHashed : ProgHOL 64 := match resolveStepLookupTail with | .seq (.ite _ body _) _ => body | _ => .skip

theorem source_resolve_step_entry : resolveStepAt 0 =
  .dec (ofString "it") (.comb [.one,.one,.one,.one]) (.rstruct [.const 0,.const 0,.const 0,.const 0])
    (.dec (ofString "e") .one (.const 0) (resolveStepAt 2)) := by
  simp only [resolveStepAt,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_resolve_step_parse_sequence : resolveStepAt 2 = .seq resolveStepParseCall (resolveStepAt 3) := by
  simp only [resolveStepParseCall,resolveStepAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_resolve_step_parse_call : resolveStepParseCall =
  .call (some (some (.local,ofString "it"),some (ofString "RlpErr",ofString "e",
    .call (some (none,none)) (ofString "mpt_fail") [.const 3])))
    (ofString "rlp_item") [.var .local (ofString "p"),.var .local (ofString "n")] := by
  simp only [resolveStepParseCall,resolveStepAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_resolve_step_kind : resolveStepAt 3 =
  .seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0)) resolveStepStringBranch .skip)
    (.return (.rstruct [.const 1,.var .local (ofString "p"),.var .local (ofString "n"),.const 0])) := by
  simp only [resolveStepAt,resolveStepStringBranch,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_resolve_step_string : resolveStepStringBranch =
  .seq (.ite (.cmp .equal (.rfield 2 (.var .local (ofString "it"))) (.const 0))
    (.return (.rstruct [.const 0,.const 0,.const 0,.const 0])) .skip)
  (.seq (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "it"))) (.const 32))
    (.call (some (none,none)) (ofString "mpt_fail") [.const 10]) .skip) resolveStepLookup) := by
  simp only [resolveStepStringBranch,resolveStepLookup,resolveStepAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_resolve_step_lookup : resolveStepLookup =
  .decCall (ofString "r") (.comb [.one,.one,.one]) (ofString "nodedb_lookup")
    [.var .local (ofString "db"),.rfield 1 (.var .local (ofString "it"))] resolveStepLookupTail := by
  simp only [resolveStepLookup,resolveStepStringBranch,resolveStepLookupTail,resolveStepAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_resolve_step_lookup_tail : resolveStepLookupTail =
  .seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) resolveStepHashed .skip)
    (.return (.rstruct [.const 1,.rfield 1 (.var .local (ofString "r")),
      .rfield 2 (.var .local (ofString "r")),.rfield 1 (.var .local (ofString "it"))])) := by
  simp only [resolveStepLookupTail,resolveStepHashed,resolveStepLookup,resolveStepStringBranch,resolveStepAt,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_resolve_step_hashed : resolveStepHashed =
  .decCall (ofString "hn") .one (ofString "node_new_hashed") [.rfield 1 (.var .local (ofString "it"))]
    (.return (.rstruct [.const 0,.var .local (ofString "hn"),.const 0,.const 0])) := by
  simp only [resolveStepHashed,resolveStepLookupTail,resolveStepLookup,resolveStepStringBranch,resolveStepAt,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_resolve_step_entry
#print axioms source_resolve_step_parse_call
#print axioms source_resolve_step_parse_sequence
#print axioms source_resolve_step_kind
#print axioms source_resolve_step_string
#print axioms source_resolve_step_lookup
#print axioms source_resolve_step_lookup_tail
#print axioms source_resolve_step_hashed
end InitECandidate.Runtime
