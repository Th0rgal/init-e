import InitECandidate.Runtime.MptInsertLeafMemeqNormalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptInsertLeafEqualTest : ProgHOL 64:=
 match mptInsertLeafAt 2 with | .seq first _=>first | _=>.skip

theorem source_mpt_insert_leaf_equal_test : mptInsertLeafEqualTest=
 .ite (.cmp .equal (.var .local (ofString "el")) (.var .local (ofString "rl")))
  (.decCall (ofString "eq") .one (ofString "memeq")
   [.var .local (ofString "ek"),.var .local (ofString "rk"),.var .local (ofString "el")]
   mptInsertLeafEqualReturn) .skip :=rfl

/-- The actual initial length test and optional memeq in leaf insertion
preserve the source context on normal fallthrough, including all unequal-length
paths, with clock cost at most the original comparison bound. -/
theorem mpt_insert_leaf_equal_test_normal_frame {F : Type}
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
  mptInsertLeafEqualTest=(none,post)) :
 post.memory=s.memory ∧post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 s.clock≤post.clock+4*length.toNat+1 ∧post.clock≤s.clock ∧
 (∀name : MlS,name≠ofString "eq"→post.locals.lookup name=s.locals.lookup name) := by
 rw [source_mpt_insert_leaf_equal_test,evaluateHOLFiniteState_ite] at run
 split at run
 · split at run
   · rw [evaluateHOLFiniteState_skip] at run
     have same : post=s:=(Prod.mk.inj run).2.symm
     subst post
     exact ⟨rfl,rfl,rfl,rfl,rfl,by omega,by omega,by intro name different;rfl⟩
   · exact mpt_insert_leaf_memeq_normal_frame s post live extensions branches size frontier
      node oldKey key length value valueLength world kinds paths nodeLive tag atNode atOldKey atOldLength
      atKey atValue atValueLength fullDomain code small budget run
 · simp at run

#print axioms mpt_insert_leaf_equal_test_normal_frame
end InitECandidate.Runtime
