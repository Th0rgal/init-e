import InitECandidate.Runtime.NodedbConstructorBound
import InitECandidate.Runtime.KeccakFullCallBound
import InitECandidate.Runtime.NormalLocalAddCalls
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def nodedbSliceAddress : ExpHOL 64 := .op .add [.var .local (ofString "slice_arr"),
  .panop .mul [.var .local (ofString "i"),.const 16]]
def nodedbHashArguments : List (ExpHOL 64) := [.load .one nodedbSliceAddress,
  .load .one (.op .add [.var .local (ofString "slice_arr"),
    .panop .mul [.var .local (ofString "i"),.const 16],.const 8]),.var .global (ofString "mpt_hash_scratch")]
def nodedbSetArguments : List (ExpHOL 64) := [.var .local (ofString "t"),
  .var .global (ofString "mpt_hash_scratch"),nodedbSliceAddress]
def nodedbInsertionBody : ProgHOL 64 := .seq
  (.call (some (none,none)) (ofString "keccak256") nodedbHashArguments)
  (.seq (.call (some (none,none)) (ofString "htab_set") nodedbSetArguments)
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))
def nodedbInsertionCondition : ExpHOL 64 := .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))
def nodedbInsertionLoop : ProgHOL 64 := .while nodedbInsertionCondition nodedbInsertionBody

theorem source_nodedb_insertion : nodedbAt 3 = .dec (ofString "i") .one (.const 0)
    (.seq nodedbInsertionLoop (.return (.var .local (ofString "t")))) := rfl

/-- Each normally completed original insertion advances the caller index once,
even though its two callees have their own locals. -/
theorem nodedb_insertion_add : NormalLocalAdd (ofString "i") 1 nodedbInsertionBody := by
  apply normalLocalAdd_seq_normal_frame
  · intro F state post run
    have keep := evaluate_avoidsLocal_flowing (ofString "i")
      (.call (some (none,none)) (ofString "keccak256") nodedbHashArguments) rfl state (by rw [run]; exact Or.inl rfl)
    rw [run] at keep; exact keep
  · apply normalLocalAdd_seq_normal_frame
    · intro F state post run
      have keep := evaluate_avoidsLocal_flowing (ofString "i")
        (.call (some (none,none)) (ofString "htab_set") nodedbSetArguments) rfl state (by rw [run]; exact Or.inl rfl)
      rw [run] at keep; exact keep
    · exact normalLocalAdd_assign _ _

/-- The source hash arguments read the two words of the current decoded slice. -/
theorem eval_nodedb_hash_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index source size output : BitVec 64)
    (atArray : state.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atOutput : state.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (sourceDomain : state.memaddrs (array + index * (16#64)))
    (sizeDomain : state.memaddrs (array + index * (16#64) + (8#64)))
    (sourceCell : state.memory (array + index * (16#64)) = .word source)
    (sizeCell : state.memory (array + index * (16#64) + (8#64)) = .word size) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) nodedbHashArguments =
      some [.val (.word source),.val (.word size),.val (.word output)] := by
  rw [evalListHOLFinite_eq_toExact]
  simp [nodedbHashArguments,nodedbSliceAddress,evalListHOLExact,evalHOLExact,atArray,atIndex,atOutput,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
    sourceDomain,sizeDomain,sourceCell,sizeCell]
  have sizeDomainRight : state.memaddrs (array + (index * (16#64) + (8#64))) := by simpa only [BitVec.add_assoc] using sizeDomain
  simp [sourceDomain,sizeDomainRight,sourceCell,sizeCell,← BitVec.add_assoc]
  rw [if_pos sizeDomainRight]

/-- The actual insertion's hash call is input-linearly bounded. It does not
require the slice bytes to be readable or the external hash call to succeed. -/
theorem runBounded_nodedb_hash {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad array index source size output : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (atState : state.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atArray : state.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atOutput : state.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (sourceDomain : state.memaddrs (array + index * (16#64))) (sizeDomain : state.memaddrs (array + index * (16#64) + (8#64)))
    (sourceCell : state.memory (array + index * (16#64)) = .word source)
    (sizeCell : state.memory (array + index * (16#64) + (8#64)) = .word size)
    (small : size.toNat ≤ 134217712) (outAligned : output.toNat % 8 = 0)
    (budget : (size.toNat * 20 + 124) + 1 ≤ state.clock) :
    RunBounded state (.call (some (none,none)) (ofString "keccak256") nodedbHashArguments)
      ((size.toNat * 20 + 124) + 1) :=
  runBounded_keccak_full_call state pointer pad source size output none nodedbHashArguments atState atPad
    (eval_nodedb_hash_arguments state array index source size output atArray atIndex atOutput
      sourceDomain sizeDomain sourceCell sizeCell) small outAligned code budget

#print axioms source_nodedb_insertion
#print axioms nodedb_insertion_add
#print axioms eval_nodedb_hash_arguments
#print axioms runBounded_nodedb_hash
end InitECandidate.Runtime
