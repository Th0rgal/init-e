import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Only four caller locals are needed by the remaining transaction suffix. -/
def TransactionDecodeWitness.withLocals {F : Type} {state : PanSemStateFiniteExact 64 F}
    {array count tx kind input inputLength scratch frame : BitVec 64} {ceiling : Nat}
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (atArray : locals.lookup (ofString "arr") = state.locals.lookup (ofString "arr"))
    (atTx : locals.lookup (ofString "tx") = state.locals.lookup (ofString "tx"))
    (atType : locals.lookup (ofString "t") = state.locals.lookup (ofString "t"))
    (atIndex : locals.lookup (ofString "k") = state.locals.lookup (ofString "k")) :
    TransactionDecodeWitness {state with locals := locals} array count tx kind input inputLength scratch frame ceiling := by
  refine ⟨valid.index,valid.heap,atArray.trans valid.arrayLocal,atTx.trans valid.txLocal,atType.trans valid.typeLocal,
    atIndex.trans valid.indexLocal,valid.indexBound,?_,valid.scratchGlobal,valid.frameGlobal,valid.heapGlobal,valid.code,
    valid.arena,valid.heapArena,valid.heapBound,valid.heapAligned,valid.inputBeforeHeap,valid.arrayBeforeHeap⟩
  intro slot inside
  obtain ⟨p,n,item⟩ := valid.slices slot inside
  exact ⟨p,n,item.after_frame state _ array slot p n input inputLength rfl rfl rfl⟩

def TransactionDecodeWitness.enterScope {F : Type} {state : PanSemStateFiniteExact 64 F}
    {array count tx kind input inputLength scratch frame : BitVec 64} {ceiling : Nat}
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (name : MlS) (value : ValueHOL 64)
    (notArray : name ≠ ofString "arr") (notTx : name ≠ ofString "tx")
    (notType : name ≠ ofString "t") (notIndex : name ≠ ofString "k") :
    TransactionDecodeWitness (setVarHOLFinite name value state) array count tx kind input inputLength scratch frame ceiling := by
  exact valid.withLocals (state.locals.update (name,value))
    (by simp [HolFiniteMapExact.lookup_update,FUPDATE,notArray])
    (by simp [HolFiniteMapExact.lookup_update,FUPDATE,notTx])
    (by simp [HolFiniteMapExact.lookup_update,FUPDATE,notType])
    (by simp [HolFiniteMapExact.lookup_update,FUPDATE,notIndex])

def TransactionDecodeWitness.leaveScope {F : Type} {state : PanSemStateFiniteExact 64 F}
    {array count tx kind input inputLength scratch frame : BitVec 64} {ceiling : Nat}
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (name : MlS) (saved : Option (ValueHOL 64))
    (notArray : name ≠ ofString "arr") (notTx : name ≠ ofString "tx")
    (notType : name ≠ ofString "t") (notIndex : name ≠ ofString "k") :
    TransactionDecodeWitness {state with locals := HolFiniteMapExact.resVarEq state.locals (name,saved)}
      array count tx kind input inputLength scratch frame ceiling :=
  valid.withLocals _ (restore_other_local _ _ _ _ (Ne.symm notArray))
    (restore_other_local _ _ _ _ (Ne.symm notTx)) (restore_other_local _ _ _ _ (Ne.symm notType))
    (restore_other_local _ _ _ _ (Ne.symm notIndex))

#print axioms TransactionDecodeWitness.withLocals
#print axioms TransactionDecodeWitness.enterScope
#print axioms TransactionDecodeWitness.leaveScope
end InitECandidate.Runtime
