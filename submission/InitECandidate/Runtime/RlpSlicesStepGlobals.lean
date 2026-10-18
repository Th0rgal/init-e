import InitECandidate.Runtime.RlpUncheckedDeclarationFrame
import InitECandidate.Runtime.RlpSlicesUpdatesInvariant
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpSlices_normal_step_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer offset : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) : post.globals = state.globals := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.op .add [.var .local (ofString "p"),.var .local (ofString "off")]] = some [.val (.word (pointer + offset))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,offsetLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpSlices_step] at run
  obtain ⟨word,ready,output,_,_,globals,_,_,tail,restored⟩ := evaluate_rlpUnchecked_declaration_normal_frame state post
    (ofString "total") _ rlpSlicesUpdates (pointer + offset) args code ticks run
  apply HolFiniteMapExact.ext
  funext watched
  have supported : avoidsGlobalAssignment watched rlpSlicesUpdates = true := by
    rw [source_rlpSlices_updates,source_rlpSlices_advances]; rfl
  have kept := evaluate_avoidsGlobalAssignment watched rlpSlicesUpdates supported
    (setVarHOLFinite (ofString "total") (.val (.word word)) ready)
  rw [tail] at kept
  rw [restored]
  exact kept.trans (congrArg (fun g => g.lookup watched) globals)

#print axioms rlpSlices_normal_step_globals
end InitECandidate.Runtime
