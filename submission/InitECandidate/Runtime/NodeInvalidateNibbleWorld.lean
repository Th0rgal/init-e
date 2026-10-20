import InitECandidate.Runtime.NodeInvalidateAllocatedCall
import InitECandidate.Runtime.MptInsertBranchDescentWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A pointwise frame on the actual byte-containing cells is sufficient to
transport a nibble range; arbitrary unrelated memory may change. -/
theorem TrieNibbleRange.after_cells {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {key length : BitVec 64} (valid : TrieNibbleRange s key length)
 (memory : ∀offset : Nat,offset<length.toNat →
  post.memory (panByteAlignHOL (key+BitVec.ofNat 64 offset))=s.memory (panByteAlignHOL (key+BitVec.ofNat 64 offset)))
 (domain : post.memaddrs=s.memaddrs) (endian : post.be=s.be) : TrieNibbleRange post key length := by
 intro offset inside byte loaded
 apply valid offset inside byte
 have sameDomain:=Iff.of_eq (congrFun domain (panByteAlignHOL (key+BitVec.ofNat 64 offset)))
 by_cases accessible : s.memaddrs (panByteAlignHOL (key+BitVec.ofNat 64 offset))
 · have postAccessible:=sameDomain.mpr accessible
   simpa [panMemLoadByteHOL,accessible,postAccessible,endian,memory offset inside] using loaded
 · have postInaccessible : ¬post.memaddrs (panByteAlignHOL (key+BitVec.ofNat 64 offset)):=fun present=>accessible (sameDomain.mp present)
   simp [panMemLoadByteHOL,postInaccessible] at loaded

/-- Actual node cache invalidation preserves an aligned indexed key placed
after this record. The three metadata addresses are separated arithmetically;
no memory-frame or callee callback is assumed. -/
theorem node_invalidate_discard_nibble_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier pointer key length : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (member : pointer∈live) (capacity : 32≤size pointer)
 (nibbles : TrieNibbleRange s key length) (keyAligned : key.toNat%8=0)
 (recordBefore : pointer.toNat+32≤key.toNat) (keyExtent : key.toNat+length.toNat≤33806089496)
 (arguments : List (ExpHOL 64))
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word pointer)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "node_invalidate") arguments)=(none,post)) :
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNibbleRange post key length ∧
 post.locals=s.locals ∧post.globals=s.globals ∧
 (∀watched : BitVec 64,watched≠pointer+8 →watched≠pointer+16 →watched≠pointer+24 →post.memory watched=s.memory watched) := by
 obtain ⟨worldOut,locals,globals,frame⟩:=node_invalidate_discard_normal_world s post live extensions branches size frontier pointer world member capacity arguments args fullDomain code run
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "node_invalidate") arguments)
 rw [run] at metadata
 refine ⟨worldOut,?_,locals,globals,frame⟩
 apply nibbles.after_cells _ metadata.2.1 metadata.2.2.1
 intro offset inside
 have keyAdd : (key+BitVec.ofNat 64 offset).toNat=key.toNat+offset := by
  rw [BitVec.toNat_add,BitVec.toNat_ofNat];omega
 have lower : key.toNat≤(panByteAlignHOL (key+BitVec.ofNat 64 offset)).toNat := by
  rw [panByteAlign_toNat64,keyAdd]
  omega
 have different (off : Nat) (small : off<32) : panByteAlignHOL (key+BitVec.ofNat 64 offset)≠pointer+BitVec.ofNat 64 off := by
  intro equal
  have natural:=congrArg BitVec.toNat equal
  rw [world.layout.field_nat pointer member off (by omega)] at natural
  omega
 exact frame _ (different 8 (by decide)) (different 16 (by decide)) (different 24 (by decide))

#print axioms TrieNibbleRange.after_cells
#print axioms node_invalidate_discard_nibble_world
end InitECandidate.Runtime
