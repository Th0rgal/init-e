import InitECandidate.Runtime.Sha256BlockSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def shaBlockPackedInitializer : ExpHOL 64 :=
  match shaBlockUnpackBody with | .dec _ _ initializer _ => initializer | _ => .const 0

def shaBlockUnpackLow : ExpHOL 64 :=
  match shaBlockUnpackBody with | .dec _ _ _ (.seq (.store _ value) _) => value | _ => .const 0

def shaBlockUnpackHigh : ExpHOL 64 :=
  match shaBlockUnpackBody with | .dec _ _ _ (.seq _ (.seq (.store _ value) _)) => value | _ => .const 0

def shaBlockUnpackAddress : ExpHOL 64 :=
  .op .add [.var .local (ofString "stp"),.panop .mul [.var .local (ofString "i"),.const 16]]

theorem source_shaBlock_unpack_body : shaBlockUnpackBody =
    .dec (ofString "packed") .one shaBlockPackedInitializer
      (.seq (.store shaBlockUnpackAddress shaBlockUnpackLow)
        (.seq (.store (.op .add [.var .local (ofString "stp"),
          .panop .mul [.var .local (ofString "i"),.const 16],.const 8]) shaBlockUnpackHigh)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))) := by rfl

#print axioms source_shaBlock_unpack_body
end InitECandidate.Runtime
