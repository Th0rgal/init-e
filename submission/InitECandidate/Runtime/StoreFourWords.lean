import InitECandidate.Runtime.HashTableReadyJournal32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The original structured store writes its four word fields in order and
consumes no source clock. Expressions are evaluated in the entry state. -/
theorem evaluate_store_four_words {F : Type} (state : PanSemStateFiniteExact 64 F)
    (address a b c d : BitVec 64) (destination expression : ExpHOL 64)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) destination = some (.val (.word address)))
    (valueEval : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
        some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (domain0 : state.memaddrs address) (domain8 : state.memaddrs (address + 8))
    (domain16 : state.memaddrs (address + 16)) (domain24 : state.memaddrs (address + 24)) :
    evaluateHOLFiniteState state (.store destination expression) = (none,journalRecordPost32 state address a b c d) := by
  classical
  rw [evaluateHOLFiniteState_store,addressEval,valueEval]
  have one : state.memaddrs (address + panBytesInWord 64) := by
    simpa [panBytesInWord] using domain8
  have two : state.memaddrs (address + panBytesInWord 64 + panBytesInWord 64) := by
    simpa [panBytesInWord,BitVec.add_assoc] using domain16
  have three : state.memaddrs (address + panBytesInWord 64 + panBytesInWord 64 + panBytesInWord 64) := by
    simpa [panBytesInWord,BitVec.add_assoc] using domain24
  simp only [flattenHOL,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.cons_append,List.nil_append,panMemStoresHOL,panMemStoreHOL,if_pos domain0,if_pos one,if_pos two,if_pos three]
  simp [panBytesInWord,BitVec.add_assoc,journalRecordPost32,sourceWriteWord]
  rfl

#print axioms evaluate_store_four_words
end InitECandidate.Runtime
