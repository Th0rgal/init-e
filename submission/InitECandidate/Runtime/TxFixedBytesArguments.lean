import InitECandidate.Runtime.TxFixedBytesBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The two concrete word cells consumed by fixed-width extraction. -/
structure RlpSliceEntry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index pointer length : BitVec 64) : Prop where
  pointerDomain : state.memaddrs (array + index * 16#64)
  lengthDomain : state.memaddrs (array + index * 16#64 + 8#64)
  pointerCell : state.memory (array + index * 16#64) = .word pointer
  lengthCell : state.memory (array + index * 16#64 + 8#64) = .word length

/-- An entry survives every state change that retains its domains and two cells. -/
theorem RlpSliceEntry.after_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer length : BitVec 64) (entry : RlpSliceEntry state array index pointer length)
    (domain : post.memaddrs = state.memaddrs)
    (pointerFrame : post.memory (array + index * 16#64) = state.memory (array + index * 16#64))
    (lengthFrame : post.memory (array + index * 16#64 + 8#64) = state.memory (array + index * 16#64 + 8#64)) :
    RlpSliceEntry post array index pointer length := by
  refine ⟨?_,?_,pointerFrame.trans entry.pointerCell,lengthFrame.trans entry.lengthCell⟩
  · rw [domain]; exact entry.pointerDomain
  · rw [domain]; exact entry.lengthDomain

/-- The original argument expressions read the pointer and length from their
actual slice cells. No independent expression-evaluation certificate is needed. -/
theorem eval_txFixedBytes_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index pointer length : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (entry : RlpSliceEntry state array index pointer length) :
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) txFixedBytesArguments =
      some [.val (.word pointer),.val (.word length)] := by
  simp [txFixedBytesArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
    List.map_cons,List.map_nil]
  rw [if_pos entry.pointerDomain,entry.pointerCell]
  have d8 : state.memaddrs (array + (index * 16#64 + 8#64)) := by simpa only [BitVec.add_assoc] using entry.lengthDomain
  have c8 : state.memory (array + (index * 16#64 + 8#64)) = .word length := by simpa only [BitVec.add_assoc] using entry.lengthCell
  rw [if_pos d8,c8]

#print axioms eval_txFixedBytes_arguments
end InitECandidate.Runtime
