import InitECandidate.Runtime.MptInsertIndexedLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual installed indexed insertion call is bounded with its real
six-argument entry and every callee rejection outcome included. -/
theorem mpt_insert_indexed_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (arguments : List (ExpHOL 64)) (destination : Option (VarKind×MlS))
 (frontier node key length level valuePointer valueLength : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word node),.val (.word key),.val (.word length),.val (.word level),.val (.word valuePointer),.val (.word valueLength)])
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (nibbles : TrieNibbleRange s key length)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (nodeValid : node=0 ∨node∈live)
 (inside : level.toNat≤length.toNat)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 19*((2^64+203)+1)+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "_mpt_insert_node") arguments) (19*((2^64+203)+1)+1) := by
 have lookup:=mpt_insert_indexed_lookup s node key length level valuePointer valueLength code
 apply RunBounded.call (bodyCost:=19*((2^64+203)+1)) args budget
 intro body callee shape actual
 rw [lookup] at actual
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj actual |>.symm
 apply mpt_insert_indexed_body_bounded _ live extensions branches size frontier node key length level valuePointer valueLength
 · exact world.after_memory_globals rfl rfl
 · exact nibbles.after_frame rfl rfl rfl
 · exact fullDomain
 · exact nodeValid
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact inside
 · exact capacity
 · exact recordsBefore
 · exact aligned
 · exact keyExtent
 · exact short
 · exact code
 · change 19*((2^64+203)+1)≤s.clock-1
   omega

#print axioms mpt_insert_indexed_call_bounded
end InitECandidate.Runtime
