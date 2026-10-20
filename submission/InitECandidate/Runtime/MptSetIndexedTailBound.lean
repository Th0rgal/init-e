import InitECandidate.Runtime.MptSetInsertDispatchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem source_mpt_set_root_declaration : mptSetAt 1=
 .dec (ofString "root") .one (.load .one (.op .add [.var .local (ofString "m"),.const 0])) (mptSetAt 2) :=rfl

/-- Actual root load followed by the original non-deleting indexed mpt_set
suffix, using the concrete fresh nibble key and allocated traversal world. -/
theorem mpt_set_indexed_tail_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier table node key length valuePointer valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (nibbles : TrieNibbleRange s key length)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (nodeValid : node=0 ∨node∈live)
 (atTable : s.locals.lookup (ofString "m")=some (.val (.word table)))
 (rootAt : s.memory table=.word node) (tableBefore : table.toNat+16≤key.toNat)
 (atKey : s.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (pointerNonzero : valuePointer≠0#64) (lengthNonzero : valueLength≠0#64)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 19*((2^64+203)+1)+1≤s.clock) :
 RunBounded s (mptSetAt 1) (19*((2^64+203)+1)+1) := by
 have address : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .add [.var .local (ofString "m"),.const 0])=some (.val (.word table)) := by
  simp [evalHOLExact,evalListHOLExact,atTable,wordOpHOL,wordOp,valueIsWord,valueWord]
 have domain : s.memaddrs table:=fullDomain table (by omega)
 have loaded : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.load .one (.op .add [.var .local (ofString "m"),.const 0]))=some (.val (.word node)) := by
  rw [evalHOLExact,address]
  change @memLoadHOLExact 64 _ .one table s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.memory s.structs=_
  simp [memLoadHOLExact,domain,rootAt]
 rw [source_mpt_set_root_declaration]
 apply RunBounded.decWord s (ofString "root") _ node loaded
 let entered:=setVarHOLFinite (ofString "root") (.val (.word node)) s
 change RunBounded entered (mptSetAt 2) _
 apply mpt_set_insert_dispatch_bounded entered live extensions branches size frontier node key length valuePointer valueLength
 · exact world.after_memory_globals rfl rfl
 · exact nibbles.after_frame rfl rfl rfl
 · exact fullDomain
 · exact nodeValid
 · simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simpa (config:={decide:=true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atKey
 · simpa (config:={decide:=true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atValue
 · simpa (config:={decide:=true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atValueLength
 · exact pointerNonzero
 · exact lengthNonzero
 · exact capacity
 · exact recordsBefore
 · exact aligned
 · exact keyExtent
 · exact short
 · exact code
 · exact budget

#print axioms mpt_set_indexed_tail_bounded
end InitECandidate.Runtime
