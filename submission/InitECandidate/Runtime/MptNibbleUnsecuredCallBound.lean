import InitECandidate.Runtime.MptNibbleUnsecuredBodyBound
import InitECandidate.Runtime.OriginalMptNibbleKeyCode
import InitECandidate.Runtime.PanThreeValueLookupShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- The installed unsecured trie-key call, including callee lookup, argument
binding and call-entry clock, is input-linear for every allocation/byte outcome. -/
theorem mpt_nibble_unsecured_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (arguments : List (ExpHOL 64)) (destination : Option (VarKind×MlS)) (table key length pointer : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word table),.val (.word key),.val (.word length)])
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (unsecured : s.memory (table+8)=.word 0) (small : length.toNat+4<2^64)
 (code : s.code=originalRuntimeCode) (budget : 1+1+(length.toNat/4+4)+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "mpt_nibble_key") arguments)
  (1+1+(length.toNat/4+4)+1) := by
 have installed : s.code.lookup (ofString "mpt_nibble_key")=some
  ([(ofString "m",.one),(ofString "key",.one),(ofString "klen",.one)],sourceFunctionBody Guest.guestFn_mpt_nibble_key,.comb [.one,.one]) := by
  rw [code];exact originalRuntimeCode_mptNibbleKey_lookup
 have lookup:=pan_three_value_lookup_shape s.code.lookup (ofString "mpt_nibble_key")
  (ofString "m") (ofString "key") (ofString "klen") (sourceFunctionBody Guest.guestFn_mpt_nibble_key)
  (.comb [.one,.one]) (.word table) (.word key) (.word length) (by decide) (by decide) (by decide) installed
 apply RunBounded.call (bodyCost:=1+1+(length.toNat/4+4)) args budget
 intro body callee shape actual
 rw [lookup] at actual
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj actual |>.symm
 apply mpt_nibble_unsecured_body_bounded _ table key length pointer
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact atHeap
 · exact unsecured
 · exact small
 · exact code
 · change 1+1+(length.toNat/4+4)≤s.clock-1
   omega
/-- Indexed trie keys encoded from a machine word occupy at most nine
bytes. Their actual unsecured conversion call therefore costs at most nine
source clocks, including allocation and access-error outcomes. -/
theorem mpt_nibble_index_key_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (arguments : List (ExpHOL 64)) (destination : Option (VarKind×MlS)) (table key length pointer : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word table),.val (.word key),.val (.word length)])
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (unsecured : s.memory (table+8)=.word 0) (shortKey : length.toNat≤9)
 (code : s.code=originalRuntimeCode) (budget : 9≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "mpt_nibble_key") arguments) 9 := by
 have actualCost : 1+1+(length.toNat/4+4)+1≤9 := by omega
 exact (mpt_nibble_unsecured_call_bounded s arguments destination table key length pointer args atHeap
  unsecured (by omega) code (by omega)).weaken actualCost
#print axioms mpt_nibble_unsecured_call_bounded
#print axioms mpt_nibble_index_key_call_bounded
end InitECandidate.Runtime
