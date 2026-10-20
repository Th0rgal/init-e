import InitECandidate.Runtime.MloadReadRuntimeBound
import InitECandidate.Runtime.EvmWordDeclarationGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem mload_saturated_tail_bounded {F : Type}
 (s : PanSemStateFiniteExact 64 F) (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words) (a b c d : BitVec 64)
 (startAt : s.locals.lookup (ofString "start")=some (fundingU256 a b c d))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (code : s.code=originalRuntimeCode) (budget : 36≤s.clock) :
 RunBounded s (mloadAt 2) 36 := by
 rw [source_mload_2]
 apply runBounded_checked_declaration s (ofString "s") (ofString "sat_word") .one [.var .local (ofString "start")] (mloadAt 3) 0 35 budget
 intro values body callee returnShape actualArgs found
 have args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) [.var .local (ofString "start")]=some [fundingU256 a b c d] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,startAt]
 have same : values=[fundingU256 a b c d]:=Option.some.inj (actualArgs.symm.trans args)
 subst values
 rw [funding_sat_word_lookup s a b c d code] at found
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj found.symm
 let entry:=callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "v",fundingU256 a b c d))
 have atValue : entry.locals.lookup (ofString "v")=some (fundingU256 a b c d) := by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have evaluated:=evaluate_source_evm_sat_word entry a b c d atValue
 constructor
 · unfold RunBounded;rw [evaluated];simp [emptyLocalsHOLFinite,entry]
 · intro value post returned checked remaining
   have equal:=Prod.mk.inj (returned.symm.trans evaluated)
   have valueEq : value=.val (.word (evmSatWord a b c d)):=PanSemResultExact.returned.inj (Option.some.inj equal.1)
   have postEq : post=emptyLocalsHOLFinite entry:=equal.2
   subst value
   subst post
   let ready:=setVarHOLFinite (ofString "s") (.val (.word (evmSatWord a b c d))) {emptyLocalsHOLFinite entry with locals:=s.locals}
   have physical : EvmMemoryOperandAt ready frame words:=valid.after_context rfl rfl rfl
   exact mload_read_tail_bounded ready frame words physical (evmSatWord a b c d) (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) inside code remaining
#print axioms mload_saturated_tail_bounded
end InitECandidate.Runtime
