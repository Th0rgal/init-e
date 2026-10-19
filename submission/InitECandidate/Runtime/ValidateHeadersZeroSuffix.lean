import InitECandidate.Runtime.ValidateHeadersSecondSource
import InitECandidate.Runtime.ValidateHeadersFirstSource
import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- With no headers, both actual loops are skipped and the source suffix
needs no witness readability, input placement or parser workspace premise. -/
theorem runBounded_validate_headers_zero_suffix {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs hashes : BitVec 64)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word (0 : BitVec 64))))
    (atHs : s.locals.lookup (ofString "hs") = some (.val (.word hs)))
    (atHashes : s.locals.lookup (ofString "hashes") = some (.val (.word hashes))) :
    RunBounded s (validateHeadersAt 3) 0 := by
  rw [source_validate_headers_index_init]
  apply RunBounded.decConst
  let ready := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) s
  let reset := setVarHOLFinite (ofString "i") (.val (.word (1 : BitVec 64))) ready
  have firstCondition : evalHOLFinite ready (h := fun a => Classical.propDecidable (ready.memaddrs a)) validateHeadersFirstCondition = some (.val (.word (0 : BitVec 64))) := by
    rw [evalHOLFinite_eq_toExact]
    simp [ready,validateHeadersFirstCondition,evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      atCount,Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess]
  have secondCondition : evalHOLFinite reset (h := fun a => Classical.propDecidable (reset.memaddrs a)) validateHeadersSecondCondition = some (.val (.word (0 : BitVec 64))) := by
    rw [evalHOLFinite_eq_toExact]
    simp (config := {decide := true}) [reset,ready,validateHeadersSecondCondition,evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      atCount,Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess]
  have firstSkip : evaluateHOLFiniteState ready (.while validateHeadersFirstCondition validateHeadersFirstBody) = (none,ready) := by
    rw [evaluateHOLFiniteState_while_total,firstCondition]
    simp
  have secondSkip : evaluateHOLFiniteState reset validateHeadersSecondLoop = (none,reset) := by
    rw [validateHeadersSecondLoop,evaluateHOLFiniteState_while_total,secondCondition]
    simp
  have assigned : evaluateHOLFiniteState ready (.assign .local (ofString "i") (.const 1)) = (none,reset) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,lookupKvarHOLFinite,ready,reset,setKvarHOLFinite,
      setVarHOLFinite,isValidValueHOLFinite,shapeOfHOLExact,shapeEqHOL,HolFiniteMapExact.lookup_update,FUPDATE]
  change RunBounded ready (validateHeadersAt 4) 0
  rw [source_validate_headers_first_loop]
  have tailSource : validateHeadersAt 5 = .seq (.assign .local (ofString "i") (.const 1)) validateHeadersSecondTail := source_validate_headers_second_tail
  rw [tailSource]
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780,firstSkip]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,assigned]
  dsimp only
  unfold validateHeadersSecondTail
  rw [evaluateHOLFiniteState_seq_line780,secondSkip]
  dsimp only
  have straight := clockPreserving_of_straightLine validateHeadersSecondReturn (by rfl) reset
  have safe := evaluate_straightLine_no_timeout validateHeadersSecondReturn (by rfl) reset
  exact ⟨by simpa [ready,reset,setVarHOLFinite] using (le_of_eq straight.symm),
    by simpa [ready,reset,setVarHOLFinite] using (le_of_eq straight),safe⟩

#print axioms runBounded_validate_headers_zero_suffix
end InitECandidate.Runtime
