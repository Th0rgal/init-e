import InitECandidate.Runtime.MptSetIndexedTailBound
import InitECandidate.Runtime.ReachesRunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The full actual non-deleting indexed mpt_set, including fresh key conversion,
root load, nineteen-iteration insertion, root store and return. No successful
allocation/callee/frame/runtime premise is assumed. -/
theorem mpt_set_indexed_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (table key length pointer node valuePointer valueLength : BitVec 64)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (atTable : s.locals.lookup (ofString "m")=some (.val (.word table)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (pointerNonzero : valuePointer≠0#64) (lengthNonzero : valueLength≠0#64)
 (unsecured : s.memory (table+8)=.word 0) (rootAt : s.memory table=.word node)
 (nodeValid : node=0 ∨node∈live) (short : length.toNat≤9)
 (capacity : ∀node∈live,32≤size node)
 (keyBefore : key.toNat+length.toNat≤pointer.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (headerExtent : table.toNat+16≤pointer.toNat)
 (code : s.code=originalRuntimeCode) (budget : 9+(19*((2^64+203)+1)+1)≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_mpt_set) (9+(19*((2^64+203)+1)+1)) := by
 have reached:=mpt_set_indexed_allocated_prefix_reaches s table key length pointer live extensions branches size world
  atTable atKey atLength unsecured short keyBefore fullDomain headerExtent code (by omega)
 apply runBounded_of_reaches s _ (mptSetAt 1) _ 9 (19*((2^64+203)+1)+1) reached budget
 intro next facts tailBudget
 obtain ⟨ready,nibbles,nibbleShort,_,nextWorld⟩:=facts
 have before:=ready.before_memory short world.capped world.aligned
 rcases ready with ⟨atNibble,locals,globals,request,capped,domain,endian,installed,_⟩
 have keyExtent:=allocationGuard_sum_bound pointer (2*length) world.capped request
 have rootKept : next.memory table=.word node := by
  rw [before table (by omega)];exact rootAt
 have recordsBefore : ∀current∈live,current.toNat+32≤pointer.toNat := by
  intro current member
  have allocated:=world.allocated current member
  have bytes:=capacity current member
  omega
 apply mpt_set_indexed_tail_bounded next live extensions branches size (allocationEnd pointer (2*length)) table node pointer (2*length) valuePointer valueLength
 · exact nextWorld
 · exact nibbles
 · intro address small;rw [domain];exact fullDomain address small
 · exact nodeValid
 · exact (locals _ (by decide)).trans atTable
 · exact rootKept
 · exact headerExtent
 · exact atNibble
 · exact (locals _ (by decide)).trans atValue
 · exact (locals _ (by decide)).trans atValueLength
 · exact pointerNonzero
 · exact lengthNonzero
 · exact capacity
 · exact recordsBefore
 · exact world.aligned
 · exact keyExtent
 · exact nibbleShort
 · exact installed.trans code
 · exact tailBudget

#print axioms mpt_set_indexed_body_bounded
end InitECandidate.Runtime
