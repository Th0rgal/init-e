import InitECandidate.Runtime.RunFramesFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def memzeroDecodedBody : ProgHOL 64 :=
  match declToHOLStructural Guest.guestFn_memzero with | .function fn => fn.body | _ => .skip

def memzeroByte8Loop : ProgHOL 64 :=
  match memzeroDecodedBody with | .dec _ _ _ (.seq _ (.seq loop _)) => loop | _ => .skip

def memzeroBase : ExpHOL 64 :=
  .op .add [.var .local (ofString "dst"),.var .local (ofString "i")]

def memzeroOffset (offset : BitVec 64) : ExpHOL 64 :=
  .op .add [.var .local (ofString "dst"),.var .local (ofString "i"),.const offset]

def memzeroAdvance (stride : BitVec 64) : ProgHOL 64 :=
  .assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const stride])

def memzeroBlockCondition (stride : BitVec 64) : ExpHOL 64 :=
  .cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const stride])

def memzeroWord8Body : ProgHOL 64 :=
  .seq (.store memzeroBase (.const 0)) (memzeroAdvance 8)

def memzeroWord32Body : ProgHOL 64 :=
  .seq (.store memzeroBase (.const 0))
    (.seq (.store (memzeroOffset 8) (.const 0))
      (.seq (.store (memzeroOffset 16) (.const 0))
        (.seq (.store (memzeroOffset 24) (.const 0)) (memzeroAdvance 32))))

def memzeroByte1Body : ProgHOL 64 :=
  .seq (.storeByte memzeroBase (.const 0)) (memzeroAdvance 1)

/-- Source provenance for the aligned word loops and final byte loop. The
unrolled eight-byte loop remains a literal subtree of the original body. -/
theorem source_memzero_body : sourceFunctionBody Guest.guestFn_memzero =
    .dec (ofString "i") .one (.const 0)
      (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "dst"),.const 7]) (.const 0))
        (.seq (.while (memzeroBlockCondition 32) memzeroWord32Body)
          (.while (memzeroBlockCondition 8) memzeroWord8Body)) .skip)
        (.seq memzeroByte8Loop
          (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) memzeroByte1Body)
            (.return (.const 0))))) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_memzero,declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,
    expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,
    memzeroByte8Loop,memzeroDecodedBody,memzeroBase,memzeroOffset,memzeroAdvance,
    memzeroBlockCondition,memzeroWord8Body,memzeroWord32Body,memzeroByte1Body]
  rfl

/-- Each source counter assignment has no clock cost. -/
theorem evaluate_memzero_advance {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index stride : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    evaluateHOLFiniteState state (memzeroAdvance stride) =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index + stride))) state) := by
  simp [memzeroAdvance,evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,indexLocal,
    wordOpHOL,wordOp,valueIsWord,valueWord,isValidValueHOLExact,lookupKvarHOLExact,shapeOfHOLExact,
    shapeEqHOL,setKvarHOLFinite]

#print axioms source_memzero_body
#print axioms evaluate_memzero_advance
end InitECandidate.Runtime
