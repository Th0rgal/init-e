import InitECandidate.Runtime.WitnessResolveModeSource
import InitECandidate.Runtime.TxFixedBytesArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Resolve-mode arguments read the two real selected slice cells. -/
theorem eval_witness_resolve_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table array slot pointer length : BitVec 64)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atSlot : s.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (slice : RlpSliceEntry s array slot pointer length) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) witnessResolveArguments =
      some [.val (.word table),.val (.word pointer),.val (.word length)] := by
  simp [witnessResolveArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atTable,atArray,atSlot,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
    List.map_cons,List.map_nil]
  rw [if_pos slice.pointerDomain,slice.pointerCell]
  have d8 : s.memaddrs (array + (slot * 16#64 + 8#64)) := by simpa only [BitVec.add_assoc] using slice.lengthDomain
  have c8 : s.memory (array + (slot * 16#64 + 8#64)) = .word length := by simpa only [BitVec.add_assoc] using slice.lengthCell
  rw [if_pos d8,c8]

#print axioms eval_witness_resolve_arguments
end InitECandidate.Runtime
