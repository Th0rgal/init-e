import InitECandidate.Runtime.PanStoreChainReach
import InitECandidate.Runtime.SystemMessageGasSetup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
/-- The five actual system-environment stores, including the four-word
base-fee load/store, preserve the calling context or reject in zero clocks. -/
theorem system_environment_setup_reaches {F : Type} (s : PanSemStateFiniteExact 64 F) :
 Reaches s (systemTransactionAt 3) (fun next=>next.locals=s.locals ∧next.globals=s.globals ∧
 next.code=s.code ∧next.memaddrs=s.memaddrs) 0 (systemTransactionAt 8) := by
 have chain : StoreChain (systemTransactionAt 3) (systemTransactionAt 8) := by
  exact .cons _ _ (.cons _ _ (.cons _ _ (.cons _ _ (.cons _ _ (.nil _)))))
 exact chain.reaches s
#print axioms system_environment_setup_reaches
end InitECandidate.Runtime
