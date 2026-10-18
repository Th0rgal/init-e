import InitECandidate.Runtime.PackBytesDeclarationBound
import InitECandidate.Runtime.MerkleizeCallBound
import InitECandidate.Runtime.MerklePositiveBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrBytesVectorLongAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (statelessNext (structuralFunctionBody Guest.guestFn_htr_bytes_vector))

def htrBytesVectorLongTailCost : Nat := (merkleBodyCost + 1) + 1

def htrBytesVectorLongPackCost : Nat := packBytesBodyCost + 1 + htrBytesVectorLongTailCost

def htrBytesVectorLongBodyCost : Nat := 1 + htrBytesVectorLongPackCost

theorem source_htrBytesVectorLong_pack : htrBytesVectorLongAt 1 =
    .decCall (ofString "pk") (.comb [.one,.one]) (ofString "pack_bytes")
      [.var .local (ofString "p"),.var .local (ofString "n")] (htrBytesVectorLongAt 2) := by rfl

theorem source_htrBytesVectorLong_tail : htrBytesVectorLongAt 2 =
    .seq (.call (some (none,none)) (ofString "merkleize")
      [.rfield 0 (.var .local (ofString "pk")),.rfield 1 (.var .local (ofString "pk")),
        .rfield 1 (.var .local (ofString "pk")),.var .local (ofString "out")])
      (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
        (.return (.const 0))) := by rfl

theorem runBounded_htrBytesVectorLong_pack {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n out heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (ho : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrBytesVectorLongPackCost ≤ state.clock) :
    RunBounded state (htrBytesVectorLongAt 1) htrBytesVectorLongPackCost := by
  rw [source_htrBytesVectorLong_pack]
  apply runBounded_packBytes_declaration state (ofString "pk") _ _ htrBytesVectorLongTailCost p n heap
    (by simp [evalListHOLExact,evalHOLExact,hp,hn]) hh small heapBound code budget
  intro post atHeap postHeapBound postCode remaining
  let ready := setVarHOLFinite (ofString "pk") (.rStruct [.val (.word heap),.val (.word (packBytesCount n))])
    {post with locals := state.locals}
  have atN : ready.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simpa (config := {decide := true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using hn
  have atOut : ready.locals.lookup (ofString "out") = some (.val (.word out)) := by
    simpa (config := {decide := true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using ho
  have args : evalListHOLFinite ready (h := fun a => Classical.propDecidable (ready.memaddrs a))
      [.rfield 0 (.var .local (ofString "pk")),.rfield 1 (.var .local (ofString "pk")),
        .rfield 1 (.var .local (ofString "pk")),.var .local (ofString "out")] =
      some [.val (.word heap),.val (.word (packBytesCount n)),.val (.word (packBytesCount n)),.val (.word out)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact,evalHOLExact]
    simp (config := {decide := true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hn,ho]
  have countBound := (packBytes_lengths n small).2.1
  rw [source_htrBytesVectorLong_tail]
  exact RunBounded.seq
    (runBounded_merkleize_call ready none _ heap (packBytesCount n) (packBytesCount n) out
      (allocationEnd heap (packBytesCount n * (32#64))) args (by omega) atHeap postHeapBound
      (postCode.trans code) (by change merkleBodyCost + 1 ≤ post.clock; unfold htrBytesVectorLongTailCost at remaining; omega)) remaining (by
      intro next normal nextCode rest
      apply RunBounded.ofProg _ (nextCode.trans (postCode.trans code)) rest
      exact ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ (by decide)))

theorem source_htrBytesVectorLong_mark : htrBytesVectorLongAt 0 =
    .decCall (ofString "mark") .one (ofString "heap_mark") [] (htrBytesVectorLongAt 1) := by rfl

theorem runBounded_htrBytesVectorLong_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer n out heap : BitVec 64)
    (input : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (output : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (small : n.toNat ≤ 134217712)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrBytesVectorLongBodyCost ≤ state.clock) :
    RunBounded state (htrBytesVectorLongAt 0) htrBytesVectorLongBodyCost := by
  rw [source_htrBytesVectorLong_mark]
  refine RunBounded.decCall (by rfl) budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "heap_mark") =
      some ([],sourceFunctionBody Guest.guestFn_heap_mark,.one) := by
    rw [code]
    exact vmLookup_heap_mark
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "heap_mark") []
    (sourceFunctionBody Guest.guestFn_heap_mark) body .one returnShape [] locals installed lookup
  subst same
  constructor
  · exact RunBounded.ofProg
      (ProgBounded.straight _ (by rw [sourceFunctionBody_eq_structural]; rfl)) code (Nat.zero_le _)
  · intro value post run remaining
    have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals)
      (sourceFunctionBody Guest.guestFn_heap_mark)
    have globals := evaluate_readOnly_globals _ heapMark_readOnly (callEntryStateHOLFinite state locals)
    rw [run] at meta' globals
    change post.globals = state.globals at globals
    let next := setVarHOLFinite (ofString "mark") value {post with locals := state.locals}
    have keep (key : MlS) (different : key ≠ ofString "mark") :
        next.locals.lookup key = state.locals.lookup key := by
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    exact runBounded_htrBytesVectorLong_pack next pointer n out heap
      ((keep _ (by decide)).trans input) ((keep _ (by decide)).trans count)
      ((keep _ (by decide)).trans output)
      (by change post.globals.lookup _ = _; rw [globals]; exact heapLocal)
      small heapBound (meta'.1.trans code) remaining

#print axioms source_htrBytesVectorLong_mark
#print axioms runBounded_htrBytesVectorLong_body
#print axioms source_htrBytesVectorLong_pack
#print axioms source_htrBytesVectorLong_tail
#print axioms runBounded_htrBytesVectorLong_pack
end InitECandidate.Runtime
