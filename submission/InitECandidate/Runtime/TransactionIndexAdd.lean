import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.HashWordStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionIndexAdd (amount : BitVec 64) : ProgHOL 64 :=
  .assign .local (ofString "k") (.op .add [.var .local (ofString "k"),.const amount])

theorem transaction_index_add_run {F : Type} (state : PanSemStateFiniteExact 64 F) (index amount : BitVec 64)
    (binding : state.locals.lookup (ofString "k") = some (.val (.word index))) :
    evaluateHOLFiniteState state (transactionIndexAdd amount) =
      (none,setVarHOLFinite (ofString "k") (.val (.word (index + amount))) state) := by
  exact evaluate_local_word_assignment state (ofString "k") _ index (index + amount) binding
    (by simp [evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord])

def TransactionDecodeWitness.addIndex {F : Type} {state : PanSemStateFiniteExact 64 F}
    {array count tx kind input inputLength scratch frame : BitVec 64} {ceiling : Nat}
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (amount : BitVec 64)
    (within : valid.index.toNat + amount.toNat ≤ count.toNat) :
    TransactionDecodeWitness (setVarHOLFinite (ofString "k") (.val (.word (valid.index + amount))) state)
      array count tx kind input inputLength scratch frame ceiling := by
  refine ⟨valid.index + amount,valid.heap,?_,?_,?_,?_,?_,?_,valid.scratchGlobal,valid.frameGlobal,valid.heapGlobal,valid.code,
    valid.arena,valid.heapArena,valid.heapBound,valid.heapAligned,valid.inputBeforeHeap,valid.arrayBeforeHeap⟩
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "k" ≠ ofString "arr" by decide] using valid.arrayLocal
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "k" ≠ ofString "tx" by decide] using valid.txLocal
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "k" ≠ ofString "t" by decide] using valid.typeLocal
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · have nextNat : (valid.index + amount).toNat = valid.index.toNat + amount.toNat := by
      rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + amount.toNat < 2^64; omega)]
    rw [nextNat]; exact within
  · intro slot bounded
    obtain ⟨p,n,item⟩ := valid.slices slot bounded
    exact ⟨p,n,item.after_frame state _ array slot p n input inputLength rfl rfl rfl⟩

#print axioms transaction_index_add_run
#print axioms TransactionDecodeWitness.addIndex
end InitECandidate.Runtime
