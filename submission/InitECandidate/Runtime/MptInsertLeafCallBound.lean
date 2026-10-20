import InitECandidate.Runtime.MptInsertLeafBodyBound
import InitECandidate.Runtime.OriginalInsertIntoLeafCode
import InitECandidate.Runtime.PanFiveWordShapeLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The installed leaf-insertion call with a short indexed key, including its
entry clock, all source loads and every allocation or store rejection. -/
theorem mpt_insert_leaf_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (arguments : List (ExpHOL 64)) (destination : Option (VarKind×MlS))
 (node key length valuePointer valueLength : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word node),.val (.word key),.val (.word length),.val (.word valuePointer),.val (.word valueLength)])
 (short : length.toNat≤18) (code : s.code=originalRuntimeCode) (budget : 2^64+201≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "_insert_into_leaf") arguments) (2^64+201) := by
 have installed : s.code.lookup (ofString "_insert_into_leaf")=some
  ([(ofString "node",.one),(ofString "rk",.one),(ofString "rl",.one),(ofString "vptr",.one),(ofString "vlen",.one)],
   sourceFunctionBody Guest.guestFn__insert_into_leaf,.one) := by
  rw [code];exact originalRuntimeCode_insertIntoLeaf_lookup
 have lookup:=pan_five_word_shape_lookup s.code.lookup (ofString "_insert_into_leaf")
  (ofString "node") (ofString "rk") (ofString "rl") (ofString "vptr") (ofString "vlen")
  (sourceFunctionBody Guest.guestFn__insert_into_leaf) .one node key length valuePointer valueLength
  (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) installed
 apply RunBounded.call (bodyCost:=2^64+200) args (by omega)
 intro body callee shape actual
 rw [lookup] at actual
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj actual |>.symm
 apply mpt_insert_leaf_body_bounded _ key length
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact short
 · exact code
 · change 2^64+200≤s.clock-1
   omega

#print axioms mpt_insert_leaf_call_bounded
end InitECandidate.Runtime
