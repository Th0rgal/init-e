import InitECandidate.Runtime.SplitExtensionSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual one-nibble old-segment arm stores the already-live child;
other suffix sizes skip it. The real read supplies its slot and rejection
prevents a normal result when that byte cannot be read. -/
theorem split_extension_single_child_normal_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier branch key length matched suffix child : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (inside : matched.toNat<length.toNat)
 (member : branch∈branches) (childValid : child=0∨child∈live)
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (atKey : s.locals.lookup (ofString "seg")=some (.val (.word key)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atSuffix : s.locals.lookup (ofString "sal")=some (.val (.word suffix)))
 (atChild : s.locals.lookup (ofString "child")=some (.val (.word child)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (run : evaluateHOLFiniteState s splitExtensionSingleChild=(none,post)) :
 AllocatedTrieWorld post live extensions branches size frontier ∧
 TrieNodeKinds post live extensions branches ∧TrieNodePaths post live extensions branches size frontier ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post live size nib len frontier) := by
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "sal")) (.const 1))=
   some (.val (.word (if suffix=1#64 then 1#64 else 0#64))) := by
  simp [evalHOLExact,atSuffix,Compiler.Encoders.Asm.wordCmpHOL]
 unfold splitExtensionSingleChild at run
 rw [evaluateHOLFiniteState_ite,cmp] at run
 by_cases one : suffix=1#64
 · simp only [if_pos one,show (1#64)≠0 from by decide,if_false] at run
   cases read : @panMemLoadByteHOL 64 _ s.memory s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.be (key+matched) with
   | none=>
    simp [branchNibbleStore,evaluateHOLFiniteState_store,evalHOLExact,evalListHOLExact,
     atBranch,atKey,atMatched,read,wordOpHOL,wordOp,valueIsWord,valueWord] at run
   | some byte=>
    obtain ⟨written,stored,worldOut,kindsOut,pathsOut,_,_,_,_,_,transport⟩:=
     evaluate_branch_nibble_store_paths_world s live extensions branches size frontier world kinds paths
      (ofString "br") (ofString "seg") (ofString "pl") (ofString "child")
      branch key matched length child byte atBranch atKey atMatched atChild member childValid
      inside keyPath.nibbles read fullDomain
    have same : post=written:=(Prod.mk.inj (run.symm.trans stored)).2
    subst post
    exact ⟨worldOut,kindsOut,pathsOut,transport⟩
 · simp only [if_neg one,ite_true,evaluateHOLFiniteState_skip] at run
   have same : post=s:=(Prod.mk.inj run.symm).2
   subst post
   exact ⟨world,kinds,paths,fun _ _ path=>path⟩

#print axioms split_extension_single_child_normal_world
end InitECandidate.Runtime
