import InitECandidate.Runtime.TrieBranchChildAllocationFloor
import InitECandidate.Runtime.SplitExtensionExtChildFloorWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original conditional extension-allocation arm, with its
actual unsigned suffix-size guard and all actual constructor effects. -/
theorem split_extension_long_child_normal_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier branch key length matched suffix child : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (short : length.toNat≤18) (inside : matched.toNat<length.toNat)
 (suffixEq : suffix=length-matched)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (keyAbove : floor≤key.toNat)
 (member : branch∈branches) (childValid : child=0∨child∈live)
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (atKey : s.locals.lookup (ofString "seg")=some (.val (.word key)))
 (atPrefix : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atSuffix : s.locals.lookup (ofString "sal")=some (.val (.word suffix)))
 (atChild : s.locals.lookup (ofString "child")=some (.val (.word child)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock)
 (run : evaluateHOLFiniteState s splitExtensionLongChild=(none,post)) :
 ∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 live⊆larger ∧extensions⊆newExtensions ∧
 AllocatedTrieWorld post larger newExtensions branches newSize finish ∧
 TrieNodeKinds post larger newExtensions branches ∧
 TrieNodePaths post larger newExtensions branches newSize finish ∧
 TrieAllocationFloor post larger branches floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .lower (.const 1) (.var .local (ofString "sal")))=
   some (.val (.word (if 1<suffix.toNat then 1#64 else 0#64))) := by
  simp [evalHOLExact,atSuffix,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
 rw [source_split_extension_long_child,evaluateHOLFiniteState_ite,cmp] at run
 by_cases long : 1<suffix.toNat
 · simp only [if_pos long,show (1#64)≠0 from by decide,if_false] at run
   obtain ⟨worldOut,kindsOut,pathsOut,lowerOut,transport⟩:=split_extension_ext_child_normal_floor_world s post live extensions branches size
    frontier branch key length matched suffix child world kinds paths keyPath short inside suffixEq long floor lower heapAbove keyAbove member childValid
    atBranch atKey atPrefix atSuffix atChild fullDomain code budget run
   exact ⟨insert frontier live,insert frontier extensions,Function.update size frontier 56,allocationEnd frontier 56,
    fun _ h=>Or.inr h,fun _ h=>Or.inr h,worldOut,kindsOut,pathsOut,lowerOut,transport⟩
 · simp only [if_neg long,ite_true,evaluateHOLFiniteState_skip] at run
   have same : post=s:=(Prod.mk.inj run.symm).2
   subst post
   exact ⟨live,extensions,size,frontier,fun _ h=>h,fun _ h=>h,world,kinds,paths,lower,fun _ _ path=>path⟩

#print axioms split_extension_long_child_normal_floor_world
end InitECandidate.Runtime
