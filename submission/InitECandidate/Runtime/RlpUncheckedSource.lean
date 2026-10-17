import InitECandidate.Runtime.RlpReadLengthDeclarationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpUncheckedAfterByte : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked with
  | .dec _ _ _ body => body
  | _ => .skip

def rlpUncheckedAfterSingle : ProgHOL 64 :=
  match rlpUncheckedAfterByte with
  | .seq _ body => body
  | _ => .skip

def rlpUncheckedAfterShort : ProgHOL 64 :=
  match rlpUncheckedAfterSingle with
  | .seq _ body => body
  | _ => .skip

def rlpUncheckedLongString : ProgHOL 64 :=
  match rlpUncheckedAfterShort with
  | .seq (.ite _ body _) _ => body
  | _ => .skip

def rlpUncheckedAfterLong : ProgHOL 64 :=
  match rlpUncheckedAfterShort with
  | .seq _ body => body
  | _ => .skip

def rlpUncheckedLongList : ProgHOL 64 :=
  match rlpUncheckedAfterLong with
  | .seq _ body => body
  | _ => .skip

theorem source_rlpUnchecked_body : sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked =
    .dec (ofString "b") .one (.loadByte (.var .local (ofString "p"))) rlpUncheckedAfterByte := by
  simp only [rlpUncheckedAfterByte,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpUnchecked_long_string : rlpUncheckedLongString =
    .dec (ofString "ll") .one (.op .sub [.var .local (ofString "b"),.const 183])
      (.decCall (ofString "n") .one (ofString "rlp_read_length")
        [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
        (.return (.op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")]))) := by
  simp only [rlpUncheckedLongString,rlpUncheckedAfterShort,rlpUncheckedAfterSingle,rlpUncheckedAfterByte,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpUnchecked_long_list : rlpUncheckedLongList =
    .dec (ofString "ll2") .one (.op .sub [.var .local (ofString "b"),.const 247])
      (.decCall (ofString "n2") .one (ofString "rlp_read_length")
        [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")]
        (.return (.op .add [.const 1,.var .local (ofString "ll2"),.var .local (ofString "n2")]))) := by
  simp only [rlpUncheckedLongList,rlpUncheckedAfterLong,rlpUncheckedAfterShort,rlpUncheckedAfterSingle,rlpUncheckedAfterByte,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

end InitECandidate.Runtime
