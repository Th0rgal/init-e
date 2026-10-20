import InitECandidate.Runtime.MemeqNormalFrame
import InitECandidate.Runtime.MptInsertLeafEqualNormalWorld
import InitECandidate.Runtime.PanDecCallNormalScope
import InitECandidate.Runtime.TrieNodePathsContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual equal-length comparison declaration in leaf insertion. Normal
fallthrough has no memory/global effects and preserves all caller locals other
than its scoped comparison name, with the real memeq clock bound. -/
theorem mpt_insert_leaf_memeq_normal_frame {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node oldKey key length value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (nodeLive : node∈live) (tag : s.memory node=.word (1#64))
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atOldKey : s.locals.lookup (ofString "ek")=some (.val (.word oldKey)))
 (atOldLength : s.locals.lookup (ofString "el")=some (.val (.word length)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (small : length.toNat≤64) (budget : 4*length.toNat+1≤s.clock)
 (run : evaluateHOLFiniteState s
  (.decCall (ofString "eq") .one (ofString "memeq")
   [.var .local (ofString "ek"),.var .local (ofString "rk"),.var .local (ofString "el")]
   mptInsertLeafEqualReturn)=(none,post)) :
 post.memory=s.memory ∧post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 s.clock≤post.clock+4*length.toNat+1 ∧post.clock≤s.clock ∧
 (∀name : MlS,name≠ofString "eq"→post.locals.lookup name=s.locals.lookup name) := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "ek"),.var .local (ofString "rk"),.var .local (ofString "el")]=
   some [.val (.word oldKey),.val (.word key),.val (.word length)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atOldKey,atKey,atOldLength]
 obtain ⟨found,bodyPost,output,spent,clock,memory,globals,domains,endian,installed,tailRun,scope⟩:=
  memeq_declaration_normal_frame s post (ofString "eq") _ mptInsertLeafEqualReturn
   oldKey key length args code small budget run
 let ready:=setVarHOLFinite (ofString "eq") (.val (.word found)) {bodyPost with locals:=s.locals}
 have readyLocal (name : MlS) (different : name≠ofString "eq") : ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
 have readyWorld : AllocatedTrieWorld ready live extensions branches size frontier:=world.after_memory_globals memory globals
 have readyKinds : TrieNodeKinds ready live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;exact congrFun memory node)
 have unchanged : output=ready:=mpt_insert_leaf_equal_normal_identity ready output live extensions branches size
  frontier node value valueLength readyWorld readyKinds (paths.after_context memory domains endian) nodeLive
  ((congrFun memory node).trans tag) ((readyLocal _ (by decide)).trans atNode)
  ((readyLocal _ (by decide)).trans atValue) ((readyLocal _ (by decide)).trans atValueLength)
  (by intro address bound;change bodyPost.memaddrs address;rw [domains];exact fullDomain address bound) tailRun
 rw [unchanged] at scope
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
 · rw [scope];exact memory
 · rw [scope];exact globals
 · rw [scope];exact domains
 · rw [scope];exact endian
 · rw [scope];exact installed
 · rw [scope];exact spent
 · rw [scope];exact clock
 · intro name different
   rw [scope,saved_local_lookup_other ready.locals (ofString "eq") name _ different]
   exact readyLocal name different

#print axioms mpt_insert_leaf_memeq_normal_frame
end InitECandidate.Runtime
