import InitECandidate.Runtime.RlpUncheckedSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpSlicesLoopAndReturn : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_list_to_slices with
  | .decCall _ _ _ _ (.decCall _ _ _ _ (.dec _ _ _ (.dec _ _ _ body))) => body
  | _ => .skip

def rlpSlicesLoop : ProgHOL 64 :=
  match rlpSlicesLoopAndReturn with
  | .seq loop _ => loop
  | _ => .skip

def rlpSlicesStep : ProgHOL 64 :=
  match rlpSlicesLoop with
  | .while _ body => body
  | _ => .skip

def rlpSlicesUpdates : ProgHOL 64 :=
  match rlpSlicesStep with
  | .decCall _ _ _ _ body => body
  | _ => .skip

theorem source_rlpSlices_loop : rlpSlicesLoop =
    .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count"))) rlpSlicesStep := by
  simp only [rlpSlicesLoop,rlpSlicesStep,rlpSlicesLoopAndReturn,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpSlices_step : rlpSlicesStep =
    .decCall (ofString "total") .one (ofString "rlp_item_total_unchecked")
      [.op .add [.var .local (ofString "p"),.var .local (ofString "off")]] rlpSlicesUpdates := by
  simp only [rlpSlicesStep,rlpSlicesLoop,rlpSlicesLoopAndReturn,rlpSlicesUpdates,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

end InitECandidate.Runtime
