import InitECandidate.Runtime.StoreControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A four-limb source store changes only its four actual word addresses,
including failures at any accessibility check. -/
theorem evaluate_fourWordStore_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (address first second third fourth watched : BitVec 64)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)))
    (valueEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value =
        some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]))
    (apart0 : watched ≠ address) (apart8 : watched ≠ address + 8#64)
    (apart16 : watched ≠ address + 16#64) (apart24 : watched ≠ address + 24#64) :
    (evaluateHOLFiniteState state (.store destination value)).2.memory watched = state.memory watched := by
  have add16 : address + 8#64 + 8#64 = address + 16#64 := by rw [BitVec.add_assoc]; rfl
  have add24 : address + 16#64 + 8#64 = address + 24#64 := by rw [BitVec.add_assoc]; rfl
  rw [evaluateHOLFiniteState_store,addressEval,valueEval]
  by_cases h0 : state.memaddrs address <;>
    by_cases h8 : state.memaddrs (address + 8#64) <;>
    by_cases h16 : state.memaddrs (address + 16#64) <;>
    by_cases h24 : state.memaddrs (address + 24#64) <;>
    simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,panBytesInWord,add16,add24,
      h0,h8,h16,h24,apart0,apart8,apart16,apart24]

#print axioms evaluate_fourWordStore_memory_frame
end InitECandidate.Runtime
