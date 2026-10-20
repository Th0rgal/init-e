import InitECandidate.Runtime.SplitExtensionIncomingNonemptyWorld
import InitECandidate.Runtime.BranchPayloadStoresWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete actual incoming arm: empty suffix updates the branch payload,
otherwise the actual nibble read, collision guard and leaf constructor run. -/
theorem split_extension_new_side_normal_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier branch key length matched suffix value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (short : length.toNat≤18) (matchedBound : matched.toNat≤length.toNat)
 (suffixEq : suffix=length-matched)
 (member : branch∈branches)
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atSuffix : s.locals.lookup (ofString "kal")=some (.val (.word suffix)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 4≤s.clock)
 (run : evaluateHOLFiniteState s splitExtensionNewSide=(none,post)) :
 ∃larger : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 live⊆larger ∧AllocatedTrieWorld post larger extensions branches newSize finish ∧
 TrieNodeKinds post larger extensions branches ∧TrieNodePaths post larger extensions branches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "kal")) (.const 0))=
   some (.val (.word (if suffix=0#64 then 1#64 else 0#64))) := by
  simp [evalHOLExact,atSuffix,Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_split_extension_incoming,evaluateHOLFiniteState_ite,cmp] at run
 by_cases empty : suffix=0#64
 · simp only [if_pos empty,show (1#64)≠0 from by decide,if_false] at run
   obtain ⟨written,stored,worldOut,kindsOut,pathsOut,_,_,_,_,_,_,transport⟩:=evaluate_branch_payload_stores_world
    s live extensions branches size frontier world kinds paths (ofString "br") (ofString "vptr") (ofString "vlen")
    branch value valueLength member atBranch atValue atValueLength fullDomain
   have same : post=written:=(Prod.mk.inj (run.symm.trans stored)).2
   subst post
   exact ⟨live,size,frontier,fun _ h=>h,worldOut,kindsOut,pathsOut,transport⟩
 · simp only [if_neg empty] at run
   have suffixNat : suffix.toNat=length.toNat-matched.toNat := by
    rw [suffixEq,BitVec.toNat_sub_of_le (BitVec.le_def.mpr matchedBound)]
   have positive : 0<suffix.toNat:=by
    have ne : suffix.toNat≠0:=fun h=>empty (BitVec.eq_of_toNat_eq h)
    omega
   obtain ⟨worldOut,kindsOut,pathsOut,transport⟩:=split_extension_incoming_nonempty_normal_world
    s post live extensions branches size frontier branch key length matched suffix value valueLength
    world kinds paths keyPath short (by omega) suffixEq member atBranch atKey atMatched atSuffix atValue atValueLength
    fullDomain code (by omega) run
   exact ⟨insert frontier live,Function.update size frontier 64,allocationEnd frontier 64,
    fun _ h=>Or.inr h,worldOut,kindsOut,pathsOut,transport⟩

#print axioms split_extension_new_side_normal_world
end InitECandidate.Runtime
