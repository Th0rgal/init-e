import InitECandidate.Runtime.NodeInvalidateKindsWorld
import InitECandidate.Runtime.NodeInvalidateNibbleWorld
import InitECandidate.Runtime.TrieNodePaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real cache-invalidating call preserves every stored leaf/extension
path. Record-header and byte-cell separation discharge the exact three write
exceptions; no witness-frame or callee-preservation callback is assumed. -/
theorem node_invalidate_discard_normal_paths_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier pointer : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (member : pointer∈live) (capacity : 32≤size pointer) (arguments : List (ExpHOL 64))
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word pointer)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "node_invalidate") arguments)=(none,post)) :
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNodeKinds post live extensions branches ∧
 TrieNodePaths post live extensions branches size frontier ∧post.locals=s.locals ∧post.globals=s.globals := by
 obtain ⟨worldOut,kindsOut,locals,globals,frame⟩:=node_invalidate_discard_normal_kinds_world s post live extensions branches size frontier pointer world kinds member capacity arguments args fullDomain code run
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "node_invalidate") arguments)
 rw [run] at metadata
 refine ⟨worldOut,kindsOut,⟨paths.leafCapacity,?_⟩,locals,globals⟩
 intro node registered nonBranch
 obtain ⟨key,len,keyAt,lenAt,short,path⟩:=paths.paths node registered nonBranch
 have headerFrame (header : Nat) (which : header=32 ∨header=40) :
  post.memory (node+BitVec.ofNat 64 header)=s.memory (node+BitVec.ofNat 64 header) := by
  have headerCapacity:=paths.header_capacity world.layout node registered nonBranch
  have headerInside : header<size node:=by rcases which with rfl|rfl <;> omega
  have separate (offset : Nat) (positive : 0<offset) (small : offset<32) :
   node+BitVec.ofNat 64 header≠pointer+BitVec.ofNat 64 offset := by
   apply world.layout.fields_ne node pointer registered member header offset headerInside (by omega)
   right
   rcases which with rfl|rfl <;> omega
  exact frame _ (separate 8 (by decide) (by decide)) (separate 16 (by decide) (by decide)) (separate 24 (by decide) (by decide))
 have nibbleOut : TrieNibbleRange post key len := by
  apply path.nibbles.after_cells _ metadata.2.1 metadata.2.2.1
  intro offset inside
  have separate (field : Nat) (small : field<32) :
   panByteAlignHOL (key+BitVec.ofNat 64 offset)≠pointer+BitVec.ofNat 64 field := by
   intro same
   have natural:=congrArg BitVec.toNat same
   rw [world.layout.field_nat pointer member field (by omega)] at natural
   rcases path.separate offset inside pointer member with before|after <;> omega
  exact frame _ (separate 8 (by decide)) (separate 16 (by decide)) (separate 24 (by decide))
 refine ⟨key,len,?_,?_,short,nibbleOut,path.extent,path.separate⟩
 · rw [show node+32=node+BitVec.ofNat 64 32 from rfl,headerFrame 32 (Or.inl rfl)];exact keyAt
 · rw [show node+40=node+BitVec.ofNat 64 40 from rfl,headerFrame 40 (Or.inr rfl)];exact lenAt

#print axioms node_invalidate_discard_normal_paths_world
end InitECandidate.Runtime
