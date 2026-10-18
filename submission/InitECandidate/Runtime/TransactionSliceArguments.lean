import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionSliceArguments (arrayName indexName : MlS) : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local arrayName,.panop .mul [.var .local indexName,.const 16]]),
   .load .one (.op .add [.var .local arrayName,.panop .mul [.var .local indexName,.const 16],.const 8])]

theorem transaction_slice_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arrayName indexName : MlS) (array index pointer length : BitVec 64)
    (arrayLocal : state.locals.lookup (arrayName) = some (.val (.word array)))
    (indexLocal : state.locals.lookup (indexName) = some (.val (.word index)))
    (entry : RlpSliceEntry state array index pointer length) :
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) (transactionSliceArguments arrayName indexName) =
      some [.val (.word pointer),.val (.word length)] := by
  simp [transactionSliceArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
    List.map_cons,List.map_nil]
  rw [if_pos entry.pointerDomain,entry.pointerCell]
  have d8 : state.memaddrs (array + (index * 16#64 + 8#64)) := by simpa only [BitVec.add_assoc] using entry.lengthDomain
  have c8 : state.memory (array + (index * 16#64 + 8#64)) = .word length := by simpa only [BitVec.add_assoc] using entry.lengthCell
  rw [if_pos d8,c8]


theorem transaction_slice_arguments_from_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arrayName indexName : MlS) (array index input inputLength : BitVec 64) (count : Nat)
    (arrayLocal : state.locals.lookup arrayName = some (.val (.word array)))
    (indexLocal : state.locals.lookup indexName = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count) (inside : index.toNat < count) :
    ∃ pointer length, evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      (transactionSliceArguments arrayName indexName) = some [.val (.word pointer),.val (.word length)] ∧
      RlpSliceInputEntry state array index pointer length input inputLength := by
  obtain ⟨pointer,length,entry⟩ := valid index inside
  exact ⟨pointer,length,transaction_slice_arguments state arrayName indexName array index pointer length arrayLocal indexLocal entry.readable,entry⟩

#print axioms transaction_slice_arguments
#print axioms transaction_slice_arguments_from_prefix
end InitECandidate.Runtime
