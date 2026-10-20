import InitECandidate.Runtime.MemoryCostOneRoundingCovers
import InitECandidate.Runtime.AddSatReturnedExactContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def MemoryExpansionCheckedEndpoint (current endpoint : BitVec 64) (value : ValueHOL 64) : Prop :=
 ∃fee expansion : BitVec 64,value=.rStruct [.val (.word fee),.val (.word expansion)] ∧
  (fee≠18446744073709551615#64 → endpoint≠18446744073709551615#64 ∧endpoint.toNat≤current.toNat+expansion.toNat)
def MemoryExpansionSpan (current start size : BitVec 64) (value : ValueHOL 64) : Prop :=
 ∃fee expansion : BitVec 64,value=.rStruct [.val (.word fee),.val (.word expansion)] ∧
  (fee≠18446744073709551615#64 → start.toNat+size.toNat≤current.toNat+expansion.toNat)

/-- The original endpoint saturation guard is retained in the covered span,
so a nonMAX actual fee implies both a finite endpoint and its coverage. -/
theorem memory_cost_one_endpoint_covers {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame current endpoint : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atEndpoint : s.locals.lookup (ofString "endp")=some (.val (.word endpoint)))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (aligned : current.toNat%32=0) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 5)=(some (.returned value),post)) :
 MemoryExpansionCheckedEndpoint current endpoint value := by
 have condition : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615))=some (.val (.word (if endpoint=18446744073709551615#64 then 1 else 0))) := by
  simp [evalHOLExact,atEndpoint,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_memory_cost_one_5] at run
 rcases memory_cost_guard_returned s post _ _ 18446744073709551615 (memoryCostOneAt 6) value condition run with returned|⟨zero,tailRun⟩
 · rw [returned]
   refine ⟨18446744073709551615#64,0,rfl,?_⟩
   intro notMaximum;exact False.elim (notMaximum rfl)
 · have finite : endpoint≠18446744073709551615#64 := by intro maximum;simp [maximum] at zero
   obtain ⟨fee,expansion,returned,coverage⟩:=memory_cost_one_loaded_covers s post frame current endpoint value atFrame atEndpoint domain currentAt aligned code tailRun
   exact ⟨fee,expansion,returned,fun notMaximum=>⟨finite,coverage notMaximum⟩⟩

/-- The actual saturating-add endpoint declaration transmits coverage of the
word endpoint to the natural start+size sum. No no-overflow premise is assumed. -/
theorem memory_cost_one_added_span {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame current start size : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atStart : s.locals.lookup (ofString "s")=some (.val (.word start)))
 (atSize : s.locals.lookup (ofString "n")=some (.val (.word size)))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (aligned : current.toNat%32=0) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 4)=(some (.returned value),post)) :
 MemoryExpansionSpan current start size value := by
 rw [source_memory_cost_one_4] at run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "s"),.var .local (ofString "n")]=some [.val (.word start),.val (.word size)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atStart,atSize]
 obtain ⟨output,tailRun,scope⟩:=add_sat_returned_exact_context s post (ofString "endp") _ start size (memoryCostOneAt 5) value args code run
 let ready:=setVarHOLFinite (ofString "endp") (.val (.word (wordAddSat start size))) {s with clock:=s.clock-1}
 have atEndpoint : ready.locals.lookup (ofString "endp")=some (.val (.word (wordAddSat start size))) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨fee,expansion,returned,checked⟩:=memory_cost_one_endpoint_covers ready output frame current (wordAddSat start size) value atFrame atEndpoint domain currentAt aligned code tailRun
 refine ⟨fee,expansion,returned,?_⟩
 intro notMaximum
 obtain ⟨finite,coverage⟩:=checked notMaximum
 have belowMax : (wordAddSat start size).toNat<18446744073709551615 := by
  have bounded:=(wordAddSat start size).isLt
  have different : (wordAddSat start size).toNat≠18446744073709551615 := by
   intro same;apply finite;apply BitVec.eq_of_toNat_eq;exact same
  omega
 have sum:=wordAddSat_toNat start size
 omega
#print axioms memory_cost_one_endpoint_covers
#print axioms memory_cost_one_added_span
end InitECandidate.Runtime
