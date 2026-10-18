import InitECandidate.Runtime.TransactionDecodeWitness
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Installing a checked decoder index retains the remaining witness fields. -/
def TransactionDecodeWitness.setIndex {F : Type} {state : PanSemStateFiniteExact 64 F}
    {array count tx kind input inputLength scratch frame : BitVec 64} {ceiling : Nat}
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (index : BitVec 64) (within : index.toNat ≤ count.toNat) :
    TransactionDecodeWitness (setVarHOLFinite (ofString "k") (.val (.word index)) state)
      array count tx kind input inputLength scratch frame ceiling := by
  refine ⟨index,valid.heap,?_,?_,?_,?_,within,?_,valid.scratchGlobal,valid.frameGlobal,valid.heapGlobal,valid.code,
    valid.arena,valid.heapArena,valid.heapBound,valid.heapAligned,valid.inputBeforeHeap,valid.arrayBeforeHeap⟩
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "k" ≠ ofString "arr" by decide] using valid.arrayLocal
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "k" ≠ ofString "tx" by decide] using valid.txLocal
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "k" ≠ ofString "t" by decide] using valid.typeLocal
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro slot bounded
    obtain ⟨p,n,item⟩ := valid.slices slot bounded
    exact ⟨p,n,item.after_frame state _ array slot p n input inputLength rfl rfl rfl⟩

#print axioms TransactionDecodeWitness.setIndex
end InitECandidate.Runtime
