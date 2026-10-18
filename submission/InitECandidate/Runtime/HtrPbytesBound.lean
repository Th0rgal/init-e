import InitECandidate.Runtime.PackBytesDeclarationBound
import InitECandidate.Runtime.HtrPlistChunksCallBound
import InitECandidate.Runtime.MerklePositiveBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrPbytesAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_htr_pbytes)

def htrPbytesTailCost : Nat := (htrPlistChunksCost + 1) + 1

def htrPbytesPackCost : Nat := packBytesBodyCost + 1 + htrPbytesTailCost

def htrPbytesBodyCost : Nat := 1 + htrPbytesPackCost

theorem source_htrPbytes_pack : htrPbytesAt 1 =
    .decCall (ofString "pk") (.comb [.one,.one]) (ofString "pack_bytes")
      [.var .local (ofString "p"),.var .local (ofString "n")] (htrPbytesAt 2) := by rfl

theorem source_htrPbytes_tail : htrPbytesAt 2 =
    .seq (.call (some (none,none)) (ofString "htr_plist_chunks")
      [.rfield 0 (.var .local (ofString "pk")),.rfield 1 (.var .local (ofString "pk")),
        .var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
        (.return (.const 0))) := by rfl

theorem runBounded_htrPbytes_pack {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n out heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (ho : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrPbytesPackCost ≤ state.clock) :
    RunBounded state (htrPbytesAt 1) htrPbytesPackCost := by
  rw [source_htrPbytes_pack]
  apply runBounded_packBytes_declaration state (ofString "pk") _ _ htrPbytesTailCost p n heap
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
        .var .local (ofString "n"),.var .local (ofString "out")] =
      some [.val (.word heap),.val (.word (packBytesCount n)),.val (.word n),.val (.word out)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact,evalHOLExact]
    simp (config := {decide := true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hn,ho]
  have countBound := (packBytes_lengths n small).2.1
  rw [source_htrPbytes_tail]
  exact RunBounded.seq
    (runBounded_htrPlistChunks_call ready none _ heap (packBytesCount n) n out
      (allocationEnd heap (packBytesCount n * (32#64))) args (by omega) atHeap postHeapBound
      (postCode.trans code) (by change htrPlistChunksCost + 1 ≤ post.clock; unfold htrPbytesTailCost at remaining; omega)) remaining (by
      intro next normal nextCode rest
      apply RunBounded.ofProg _ (nextCode.trans (postCode.trans code)) rest
      exact ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ (by decide)))

theorem source_htrPbytes_mark : htrPbytesAt 0 =
    .decCall (ofString "mark") .one (ofString "heap_mark") [] (htrPbytesAt 1) := by rfl

theorem runBounded_htrPbytes_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer n out heap : BitVec 64)
    (input : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (output : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (small : n.toNat ≤ 134217712)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrPbytesBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htr_pbytes) htrPbytesBodyCost := by
  rw [sourceFunctionBody_eq_structural]
  change RunBounded state (htrPbytesAt 0) htrPbytesBodyCost
  rw [source_htrPbytes_mark]
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
    exact runBounded_htrPbytes_pack next pointer n out heap
      ((keep _ (by decide)).trans input) ((keep _ (by decide)).trans count)
      ((keep _ (by decide)).trans output)
      (by change post.globals.lookup _ = _; rw [globals]; exact heapLocal)
      small heapBound (meta'.1.trans code) remaining

#print axioms source_htrPbytes_mark
#print axioms runBounded_htrPbytes_body
#print axioms source_htrPbytes_pack
#print axioms source_htrPbytes_tail
#print axioms runBounded_htrPbytes_pack
end InitECandidate.Runtime
