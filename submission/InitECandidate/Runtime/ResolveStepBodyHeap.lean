import InitECandidate.Runtime.ResolveStepSuffixHeap
import InitECandidate.Runtime.ResolveStepReturnedContract
import InitECandidate.Runtime.NodedbContentsBetweenFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def ResolveHeapProtectedFrame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (ceiling : Nat) : Prop :=
  ∃ nextHeap : BitVec 64,
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
    heap.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧
    ∀ watched : BitVec 64, ceiling ≤ watched.toNat → watched.toNat < heap.toNat → post.memory watched = s.memory watched

theorem resolve_step_parse_kind_returned_heap {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame table heap : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : resolveStepParseCost length.toNat ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (resolveStepAt 2) = (some (.returned value),post)) :

    ResolveHeapProtectedFrame s post heap ceiling := by
  rw [source_resolve_step_parse_sequence] at run
  obtain ⟨ready,normal,tailRun⟩ := seq_returned_of_nonreturning_first
    (resolve_step_parse_call_no_return s pointer length atPointer atLength code) run
  obtain ⟨kind,key,payload,consumed,locals,starts,ends,nowrap,payloadBound,globals,memory,codeEq,domain,endian⟩ :=
    resolve_step_parse_call_normal_contract s ready pointer length scratch frame ceiling inputLimit
      atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena budget normal
  have result := resolve_step_kind_returned_heap ready post table kind key payload consumed heap
    (by rw [locals]; simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "it" ≠ ofString "db" by decide] using atTable)
    (by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE])
    ((globals _).trans atHeap) heapBound (codeEq.trans code) value tailRun
  obtain ⟨nextHeap,atNext,growth,capped,prefixFrame⟩ := result
  refine ⟨nextHeap,atNext,growth,capped,?_⟩
  intro watched above before
  exact (prefixFrame watched before).trans (memory watched above)

/-- The original returned resolver preserves the old DB arena between scratch
and the initial heap, while its actual heap frontier grows monotonically inside
the cap. No allocation-room, source-domain or callee-success premise is used. -/
theorem resolve_step_body_returned_heap_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame table heap : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : resolveStepParseCost length.toNat ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__resolve_step) = (some (.returned value),post)) :

    ResolveHeapProtectedFrame s post heap ceiling := by
  change evaluateHOLFiniteState s (resolveStepAt 0) = _ at run
  rw [source_resolve_step_entry] at run
  obtain ⟨it,first,initialized,firstRun,postEq⟩ := evaluate_dec_returned_scope s post (ofString "it") _ _ _ value run
  have itEq : it = .rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))] := by
    simpa [evalHOLExact,evalListHOLExact] using initialized.symm
  subst it
  obtain ⟨error,output,initialized,childRun,firstEq⟩ := evaluate_dec_returned_scope _ first
    (ofString "e") .one (.const 0) (resolveStepAt 2) value firstRun
  have errorEq : error = .val (.word (0#64)) := by simpa [evalHOLExact] using initialized.symm
  subst error
  let entered := setVarHOLFinite (ofString "e") (.val (.word (0#64)))
    (setVarHOLFinite (ofString "it")
      (.rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))]) s)
  have facts := resolve_step_parse_kind_returned_heap entered output pointer length scratch frame table heap ceiling inputLimit
    (by simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atPointer)
    (by simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atLength)
    (by simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTable)
    atHeap heapBound inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena budget value childRun
  rw [postEq,firstEq]
  exact facts

/-- Concrete DB metadata, value membership and input-slice records survive an
actual complete returned resolver invocation, including hashed-node fallback. -/
theorem resolve_step_body_returned_database_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame table heap : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : resolveStepParseCost length.toNat ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__resolve_step) = (some (.returned value),post))
    (dbHeap array total input inputLength : BitVec 64)
    (built : NodedbTableAt s table dbHeap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (tableAbove : ceiling ≤ table.toNat) (arrayAbove : ceiling ≤ array.toNat)
    (tableEnd : dbHeap.toNat ≤ heap.toNat) (arrayEnd : array.toNat+total.toNat*16 ≤ heap.toNat) :

    ResolveHeapProtectedFrame s post heap ceiling ∧
      NodedbTableAt post table dbHeap total ∧
      HashTableValuesIn table (NodedbSliceTargets array total) post ∧
      RlpSliceInputPrefix post array input inputLength total.toNat := by
  have frame := resolve_step_body_returned_heap_contract s post pointer length scratch frame table heap ceiling inputLimit
    atPointer atLength atTable atHeap heapBound inputRange lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena budget value run
  have metadata := evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn__resolve_step)
  rw [run] at metadata
  exact ⟨frame,nodedb_contents_after_between_frame s post table dbHeap array total input inputLength heap ceiling
    built entries slices tableAbove arrayAbove tableEnd arrayEnd metadata.2.1 metadata.2.2.1 metadata.1 frame.choose_spec.2.2.2⟩

#print axioms resolve_step_parse_kind_returned_heap
#print axioms resolve_step_body_returned_heap_contract
#print axioms resolve_step_body_returned_database_contract
end InitECandidate.Runtime
