import InitECandidate.Runtime.MemeqReadability
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_local_word_assignment {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (expression : ExpHOL 64) (old value : BitVec 64)
    (binding : state.locals.lookup name = some (.val (.word old)))
    (evaluated : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression = some (.val (.word value))) :
    evaluateHOLFiniteState state (.assign .local name expression) =
      (none,setVarHOLFinite name (.val (.word value)) state) := by
  rw [evaluateHOLFiniteState_assign]
  simp [evaluated,isValidValueHOLExact,lookupKvarHOLExact,binding,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite]

def hashWordStep (offset : Nat) : ProgHOL 64 :=
  .seq (.assign .local (ofString "w") (.load .one (memeqAddress (ofString "p") offset)))
    (.assign .local (ofString "h") (.op .xor [.var .local (ofString "h"),.var .local (ofString "w")]))

/-- The original word-at-a-time hash step only loads a key word and updates
its two locals, with no source clock or memory effect. -/
theorem evaluate_hashWordStep {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash oldWord value : BitVec 64) (offset : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (domain : state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (cell : state.memory (pointer + BitVec.ofNat 64 offset) = .word value) :
    evaluateHOLFiniteState state (hashWordStep offset) =
      (none,setVarHOLFinite (ofString "h") (.val (.word (hash ^^^ value)))
        (setVarHOLFinite (ofString "w") (.val (.word value)) state)) := by
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (memeqAddress (ofString "p") offset)) = some (.val (.word value)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_memeqAddress state (ofString "p") pointer offset pointerLocal]
    simp [memLoadHOLExact,domain,cell]
  have first := evaluate_local_word_assignment state (ofString "w") _ oldWord value wordLocal loaded
  let middle := setVarHOLFinite (ofString "w") (.val (.word value)) state
  have wh : ofString "w" ≠ ofString "h" := by decide
  have h : middle.locals.lookup (ofString "h") = some (.val (.word hash)) := by
    simpa [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,wh] using hashLocal
  have w : middle.locals.lookup (ofString "w") = some (.val (.word value)) := by
    simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have mixed : @evalHOLExact 64 F _ middle.toExact
      (fun address => Classical.propDecidable (middle.memaddrs address))
      (.op .xor [.var .local (ofString "h"),.var .local (ofString "w")]) =
        some (.val (.word (hash ^^^ value))) := by
    simp [evalHOLExact,evalListHOLExact,h,w,wordOpHOL,wordOp,valueIsWord,valueWord]
  have second := evaluate_local_word_assignment middle (ofString "h") _ hash (hash ^^^ value) h mixed
  unfold hashWordStep
  rw [evaluateHOLFiniteState_seq_line780,first]
  exact second

#print axioms evaluate_local_word_assignment
#print axioms evaluate_hashWordStep
end InitECandidate.Runtime
