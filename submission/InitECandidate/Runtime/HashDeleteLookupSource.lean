import InitECandidate.Runtime.HashDeleteCapacityScopeLinked32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

theorem source_hashDelete_lookup_prefix : sourceFunctionBody Guest.guestFn_htab_del =
    .decCall (ofString "i") .one (ofString "htab_find_slot")
      [.var .local (ofString "t"),.var .local (ofString "key")]
      (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16))
        (.seq hashDeleteMissingGuard hashDeleteFoundHeaderScopes)) := by
  unfold hashDeleteMissingGuard hashDeleteFoundHeaderScopes hashDeleteFinalTail
    hashDeleteLoop hashDeleteLoopBody hashDeleteLoopRest hashOrderAddress hashLocalAddress
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,Option.orElse,hashDeleteLeadingWhile,
    sourceFindLocalScope,hashDeleteEmpty,hashProbeStep]
  rfl

#print axioms source_hashDelete_lookup_prefix
end InitECandidate.Runtime
