import InitECandidate.Runtime.SSAQuantitativeReturningNone
import InitECandidate.Runtime.SSAReturningHandlerOutcomesCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 8000000
set_option pp.structureInstances false

/-- Actual normal-return and exception-binding compiler contexts. The handler
counter follows compilation of the normal continuation, as in ssaCcTrans. -/
noncomputable def ssaReturningSomeContexts (program : WordLangProgHOL (BitVec 64))
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)) :
    (Spt Nat × Nat) × (Spt Nat × Nat) :=
  match program with
  | .call (some (returns,names,body,_,_)) _ _ (some (exceptionVar,_,_,_)) =>
    let allNames := sptUnion names.1 names.2
    let keys := (sptToAList allNames).map Prod.fst
    let stack := listNextVarRenameMove (width := 64) map (next+2) keys
    let refresh := listNextVarRenameMove (width := 64) (sptInter stack.2.1 allNames) (stack.2.2+2) keys
    let bindings := listNextVarRename returns refresh.2.1 refresh.2.2
    let normal := ssaCcTrans body bindings.2.1 bindings.2.2 tables
    let exception := nextVarRename exceptionVar refresh.2.1 normal.2.2
    ((bindings.2.1,bindings.2.2),(exception.2.1,exception.2.2))
  | _ => ((map,next),(map,next))

/-- Exact emitted caller prefix and the larger of the selected continuation
budgets, including actual reconciliation leaves and root-only body allowances. -/
noncomputable def ssaReturningSomeEntryPrice (TP : WordLangProgHOL (BitVec 64) → Nat)
    (bodyEntry handlerEntry : Spt Nat → Nat → Nat) (program : WordLangProgHOL (BitVec 64))
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)) : Nat :=
  let contexts := ssaReturningSomeContexts program map next tables
  match (ssaCcTrans program map next tables).1 with
  | .seq stackMove (.seq argMove (.call (some (regs,names,normal,l1,l2)) dest args
      (some (reg,exception,h1,h2)))) =>
    match normal,exception with
    | .seq (.seq refresh (.seq binder _)) moves,
      .seq (.seq exceptionRefresh (.seq exceptionBinder _)) exceptionMoves =>
      TP stackMove + TP argMove + TP (.call (some (regs,names,normal,l1,l2)) dest args
        (some (reg,exception,h1,h2))) +
        max (TP refresh + TP binder + bodyEntry contexts.1.1 contexts.1.2 + ssaReconciliationPrice TP moves)
          (TP exceptionRefresh + TP exceptionBinder + handlerEntry contexts.2.1 contexts.2.2 +
            ssaReconciliationPrice TP exceptionMoves)
    | _,_ => 0
  | _ => 0

#print axioms ssaReturningSomeContexts
#print axioms ssaReturningSomeEntryPrice
end InitECandidate.Runtime.FineCost
