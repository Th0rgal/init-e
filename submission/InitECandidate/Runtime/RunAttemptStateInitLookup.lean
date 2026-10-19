import InitECandidate.Runtime.OriginalStateInitCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stateInitCallee (nodeTable stateRoot codeTable : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  ((HolFiniteMapExact.empty.update (ofString "nodedb",.val (.word nodeTable))).update
    (ofString "state_root",.val (.word stateRoot))).update (ofString "codedb",.val (.word codeTable))

/-- The frozen code installs the actual initializer body and its three parameter bindings. -/
theorem lookup_state_init_callee (nodeTable stateRoot codeTable : BitVec 64) :
    lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "state_init")
      [.val (.word nodeTable),.val (.word stateRoot),.val (.word codeTable)] =
      some (sourceFunctionBody Guest.guestFn_state_init,stateInitCallee nodeTable stateRoot codeTable,.one) := by
  exact pan_three_word_lookup originalRuntimeCode.lookup (ofString "state_init")
    (ofString "nodedb") (ofString "state_root") (ofString "codedb")
    (sourceFunctionBody Guest.guestFn_state_init) nodeTable stateRoot codeTable (by decide) (by decide) (by decide)
    originalRuntimeCode_stateInit_lookup

#print axioms lookup_state_init_callee
end InitECandidate.Runtime
