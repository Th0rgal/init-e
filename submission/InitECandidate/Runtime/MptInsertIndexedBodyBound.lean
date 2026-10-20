import InitECandidate.Runtime.MptInsertRankedLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The whole original insertion function on a concrete allocated indexed
trie has a finite uniform source-clock bound. This includes initialization,
all nineteen possible iterations, every rejection outcome, and the return. -/
theorem mpt_insert_indexed_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier node key length level valuePointer valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (nibbles : TrieNibbleRange s key length)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (nodeValid : node=0 ∨node∈live)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (inside : level.toNat≤length.toNat)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 19*((2^64+203)+1)≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn__mpt_insert_node) (19*((2^64+203)+1)) := by
 let ready:=setVarHOLFinite (ofString "go") (.val (.word (1#64)))
  (setVarHOLFinite (ofString "slot") (.val (.word (0#64)))
   (setVarHOLFinite (ofString "result") (.val (.word (0#64))) s))
 have kept (name : MlS) (a : name≠ofString "go") (b : name≠ofString "slot") (c : name≠ofString "result") :
  ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,a,b,c,Ne.symm a,Ne.symm b,Ne.symm c]
 have active : MptInsertActive ready live extensions branches size frontier key length valuePointer valueLength (length.toNat-level.toNat+1) := by
  refine ⟨world.after_memory_globals rfl rfl,nibbles.after_frame rfl rfl rfl,fullDomain,
   (kept _ (by decide) (by decide) (by decide)).trans atKey,
   (kept _ (by decide) (by decide) (by decide)).trans atLength,
   (kept _ (by decide) (by decide) (by decide)).trans atValue,
   (kept _ (by decide) (by decide) (by decide)).trans atValueLength,node,0,level,0,
   (kept _ (by decide) (by decide) (by decide)).trans atNode,?_,
   (kept _ (by decide) (by decide) (by decide)).trans atLevel,?_,nodeValid,Or.inl rfl,?_,?_,inside,rfl⟩
  · simp (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro impossible;exact False.elim (impossible rfl)
  · intro impossible;exact False.elim (impossible rfl)
 rw [source_mptInsert_body]
 apply RunBounded.decConst
 apply RunBounded.decConst
 apply RunBounded.decConst
 change RunBounded ready (.seq (.while mptInsertCondition mptInsertLoopStep) (.return (.var .local (ofString "result")))) _
 refine RunBounded.seq (state:=ready) (a:=19*((2^64+203)+1)) (b:=0) ?_ (by exact budget) ?_
 · exact mpt_insert_indexed_loop_bounded ready live extensions branches size frontier key length valuePointer valueLength _ active
    capacity recordsBefore aligned keyExtent short code budget
 · intro next _ nextCode _
   exact ProgBounded.straight _ rfl next (nextCode.trans code) (Nat.zero_le _)

#print axioms mpt_insert_indexed_body_bounded
end InitECandidate.Runtime
