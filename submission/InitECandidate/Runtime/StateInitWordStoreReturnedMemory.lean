import InitECandidate.Runtime.WordStoreNormalMemory
import InitECandidate.Runtime.AllocationFramedGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem state_init_word_store_returned_reaches {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (destination expression : ExpHOL 64) (address word : BitVec 64) (floor : Nat) (tail : ProgHOL 64) (value : ValueHOL 64)
 (atAddress : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) destination=some (.val (.word address)))
 (atWord : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some (.val (.word word)))
 (above : floor≤address.toNat)
 (run : evaluateHOLFiniteState s (.seq (.store destination expression) tail)=(some (.returned value),post)) :
 ∃ready : PanSemStateFiniteExact 64 F,evaluateHOLFiniteState ready tail=(some (.returned value),post) ∧
 ready.globals=s.globals ∧ready.code=s.code ∧ready.memaddrs=s.memaddrs ∧
 (∀watched : BitVec 64,watched.toNat<floor→ ready.memory watched=s.memory watched) := by
 obtain ⟨ready,normal,returned⟩:=seq_returned_of_first (evaluate_store_control_frame s destination expression).1 run
 have frame:=evaluate_word_store_normal_memory s ready destination expression address word atAddress atWord normal
 have metadata:=evaluateHOLFiniteState_metadata s (.store destination expression)
 rw [normal] at metadata
 have globals : (evaluateHOLFiniteState s (.store destination expression)).2.globals=s.globals := by
  rw [evaluateHOLFiniteState_store]
  repeat first | split | rfl
 rw [normal] at globals
 refine ⟨ready,returned,globals,metadata.1,metadata.2.1,?_⟩
 intro watched below
 exact frame.2 watched (by intro same;subst watched;omega)
#print axioms state_init_word_store_returned_reaches
end InitECandidate.Runtime
