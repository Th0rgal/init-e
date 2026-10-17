import InitECandidate.Runtime.HashDeleteHeaderScopesLinked32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

/-- The evaluated header/saved-position/scan suffix is the original source scope. -/
theorem source_hashDelete_found_header_scope :
    sourceFindLocalScope (ofString "klen") (sourceFunctionBody Guest.guestFn_htab_del) =
      some hashDeleteFoundHeaderScopes := by
  unfold hashDeleteFoundHeaderScopes hashDeleteFinalTail
    hashDeleteLoop hashDeleteLoopBody hashDeleteLoopRest hashOrderAddress hashLocalAddress
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,Option.orElse,hashDeleteLeadingWhile,
    sourceFindLocalScope,hashDeleteEmpty,hashProbeStep]
  rfl

theorem source_hashDelete_capacity_scope :
    sourceFindLocalScope (ofString "cap") (sourceFunctionBody Guest.guestFn_htab_del) =
      some (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16))
        (.seq (.ite (.cmp .equal (.var .local (ofString "i")) (.var .local (ofString "cap")))
          (.return (.const 0)) .skip) hashDeleteFoundHeaderScopes)) := by
  unfold hashDeleteFoundHeaderScopes hashDeleteFinalTail
    hashDeleteLoop hashDeleteLoopBody hashDeleteLoopRest hashOrderAddress hashLocalAddress
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,Option.orElse,hashDeleteLeadingWhile,
    sourceFindLocalScope,hashDeleteEmpty,hashProbeStep]
  rfl

#print axioms source_hashDelete_capacity_scope
#print axioms source_hashDelete_found_header_scope
end InitECandidate.Runtime
