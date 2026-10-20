import InitECandidate.Runtime.SplitExtensionLeafChildWorld
import InitECandidate.Runtime.MptFailGuardNormalIdentity
import InitECandidate.Runtime.PanDecNormalScope
import InitECandidate.Runtime.HtabDelBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual incoming nibble declaration, collision rejection, leaf allocation
and child store; the small slot is earned from the real read, not assumed. -/
theorem split_extension_incoming_nonempty_normal_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier branch key length matched suffix value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (short : length.toNat≤18) (inside : matched.toNat<length.toNat)
 (suffixEq : suffix=length-matched)
 (member : branch∈branches)
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atSuffix : s.locals.lookup (ofString "kal")=some (.val (.word suffix)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock)
 (run : evaluateHOLFiniteState s splitExtensionIncomingNonempty=(none,post)) :
 AllocatedTrieWorld post (insert frontier live) extensions branches
  (Function.update size frontier 64) (allocationEnd frontier 64) ∧
 TrieNodeKinds post (insert frontier live) extensions branches ∧
 TrieNodePaths post (insert frontier live) extensions branches
  (Function.update size frontier 64) (allocationEnd frontier 64) ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→
  TriePathBuffer post (insert frontier live) (Function.update size frontier 64) nib len (allocationEnd frontier 64)) := by
 obtain ⟨found,output,initialized,bodyRun,postEq⟩:=evaluate_dec_normal_scope s post (ofString "idx") .one
  (.loadByte (.op .add [.var .local (ofString "rk"),.var .local (ofString "pl")]))
  (.seq splitExtensionCollisionGuard splitExtensionLeafChildBody) run
 cases read : @panMemLoadByteHOL 64 _ s.memory s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.be (key+matched) with
 | none=>
  simp [evalHOLExact,evalListHOLExact,atKey,atMatched,read,wordOpHOL,wordOp,valueIsWord,valueWord] at initialized
 | some byte=>
  have initializer : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
   (.loadByte (.op .add [.var .local (ofString "rk"),.var .local (ofString "pl")]))=
    some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
   simp [evalHOLExact,evalListHOLExact,atKey,atMatched,read,wordOpHOL,wordOp,valueIsWord,valueWord]
  have valueEq : found=.val (.word (BitVec.ofNat 64 byte.toNat)):=Option.some.inj (initialized.symm.trans initializer)
  subst found
  let ready:=setVarHOLFinite (ofString "idx") (.val (.word (BitVec.ofNat 64 byte.toNat))) s
  change evaluateHOLFiniteState ready (.seq splitExtensionCollisionGuard splitExtensionLeafChildBody)=(none,output) at bodyRun
  obtain ⟨middle,guardRun,leafRun⟩:=seq_normal_parts bodyRun
  have readyCode : ready.code=originalRuntimeCode:=code
  have middleEq : middle=ready:=mpt_fail_guard_normal_identity ready middle _ 11 readyCode guardRun
  subst middle
  have small : byte.toNat<16:=keyPath.nibbles matched.toNat inside byte (by simpa using read)
  have slotSmall : (BitVec.ofNat 64 byte.toNat).toNat<16 := by
   rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
   exact small
  have readyLocal (name : MlS) (separate : name≠ofString "idx") : ready.locals.lookup name=s.locals.lookup name := by
   simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,separate,Ne.symm separate]
  have readyWorld : AllocatedTrieWorld ready live extensions branches size frontier:=world.after_memory_globals rfl rfl
  have readyKinds : TrieNodeKinds ready live extensions branches:=
   kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;rfl)
  obtain ⟨worldOut,kindsOut,pathsOut,transport⟩:=split_extension_leaf_child_normal_world ready output live extensions branches size
   frontier branch key length matched suffix (BitVec.ofNat 64 byte.toNat) value valueLength readyWorld readyKinds
   (paths.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl) short inside suffixEq slotSmall member
   ((readyLocal _ (by decide)).trans atBranch) ((readyLocal _ (by decide)).trans atKey)
   ((readyLocal _ (by decide)).trans atMatched) ((readyLocal _ (by decide)).trans atSuffix)
   (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   ((readyLocal _ (by decide)).trans atValue) ((readyLocal _ (by decide)).trans atValueLength)
   fullDomain readyCode budget leafRun
  have memory : post.memory=output.memory:=by rw [postEq]
  have globals : post.globals=output.globals:=by rw [postEq]
  have domain : post.memaddrs=output.memaddrs:=by rw [postEq]
  have endian : post.be=output.be:=by rw [postEq]
  refine ⟨worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domain endian,?_⟩
  · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node member;rw [memory])
  · intro nib len path
    exact (transport nib len (path.after_context rfl rfl rfl)).after_context memory domain endian

#print axioms split_extension_incoming_nonempty_normal_world
end InitECandidate.Runtime
