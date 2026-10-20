import InitECandidate.Runtime.U256StoreUpperFrame
import InitECandidate.Runtime.U256ZeroFundingValue
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual checked U256 writer call protects all old upper-arena cells and
keeps every global, including at unaligned destinations. -/
theorem u256_store_discard_normal_upper {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (arguments : List (ExpHOL 64)) (a b c d destination watched : BitVec 64) (frontier : Nat)
 (args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [fundingU256 a b c d,.val (.word destination)])
 (extent : destination.toNat+32≤frontier) (cap : frontier≤2^64)
 (above : frontier≤watched.toNat)
 (code : s.code=originalRuntimeCode) (domain : DomOK s.memaddrs)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "u256_to_be32") arguments)=(none,post)) :
 post.memory watched=s.memory watched ∧post.globals=s.globals ∧post.locals=s.locals := by
 let callee:=(HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)).update (ofString "out",.val (.word destination))
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "u256_to_be32") [fundingU256 a b c d,.val (.word destination)]=some (sourceFunctionBody Guest.guestFn_u256_to_be32,callee,.one) := by
  apply lookupCodeFinite_of_exact
  rw [code]
  simp (config:={decide:=true}) [lookupCodeHOLExact,vmLookup_u256_to_be32,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
  funext key
  by_cases out : key=ofString "out"
  · subst key;simp (config:={decide:=true}) [callee,HolFiniteMapExact.lookup_update,FUPDATE]
  · by_cases first : key=ofString "a"
    · subst key;simp (config:={decide:=true}) [callee,HolFiniteMapExact.lookup_update,FUPDATE,fundingU256]
    · simp [callee,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,out,first,Ne.symm out,Ne.symm first]
 obtain ⟨returned,body,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "u256_to_be32") arguments _ _ callee .one args lookup run
 obtain ⟨other,otherBody,otherRun,globals,_⟩:=evaluate_discard_normal_body s post (ofString "u256_to_be32") arguments _ _ callee .one args lookup run
 have equal : otherBody=body:=(Prod.mk.inj (bodyRun.symm.trans otherRun)).2.symm
 subst otherBody
 let entry:=callEntryStateHOLFinite s callee
 have atDestination : entry.locals.lookup (ofString "out")=some (.val (.word destination)) := by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have frame:=u256_store_body_upper_memory entry destination watched frontier extent cap above atDestination code domain
 rw [bodyRun] at frame
 have spec:=u2b_wn (D:=s.memaddrs) (B:=s.be) (A:=fun G=>G=s.globals) (w:=watched) destination (u256_store_window_below destination watched frontier extent cap above)
 have continued:=(spec F entry code ⟨domain,rfl,rfl⟩ rfl (by intro name impossible;exact False.elim impossible) entry.globals rfl atDestination).2.1
 rw [bodyRun] at continued
 have kept:=continued (Or.inr (Or.inr (Or.inr ⟨returned,rfl⟩)))
 exact ⟨memory ▸ frame,globals.trans kept,locals⟩
#print axioms u256_store_discard_normal_upper
end InitECandidate.Runtime
