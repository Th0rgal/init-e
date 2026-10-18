import InitECandidate.Runtime.StoreChainReturnedLocal
import InitECandidate.Runtime.PayloadWithdrawalsReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The final original payload stores return the unchanged payload pointer. -/
theorem payload_store_tail_returned_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (run : evaluateHOLFiniteState state (payloadAt 20) = (some (.returned value),post)) :
    value = .val (.word payload) := by
  apply evaluate_storeChain_returned_local (key := ofString "pl") ?_ state post payload value atPayload run
  simp only [payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  change StoreChainReturnedLocal (ofString "pl") (.seq (.store _ _) _)
  repeat first | apply StoreChainReturnedLocal.store | exact StoreChainReturnedLocal.finish

/-- Withdrawal counting cannot change the payload pointer returned by its
following stores, even when the initial clock is below the success bound. -/
theorem payload_withdrawals_returned_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload withdrawals balance : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 19) = (some (.returned value),post)) :
    value = .val (.word payload) := by
  obtain ⟨_,_,bodyPost,output,tail,_,_,_⟩ :=
    payload_withdrawals_suffix_returned state post withdrawals balance value atWithdrawals atBalance code run
  apply payload_store_tail_returned_value _ output payload value ?_ tail
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atPayload,
    show ofString "nwd" ≠ ofString "pl" by decide]

#print axioms payload_store_tail_returned_value
#print axioms payload_withdrawals_returned_value
end InitECandidate.Runtime
