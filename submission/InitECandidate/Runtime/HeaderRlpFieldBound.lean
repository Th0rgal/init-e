import InitECandidate.Runtime.RlpItemDeclarationBound
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.StatelessInputSource
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

inductive HeaderRlpField where
  | uint | bytes | raw

def headerRlpFieldDeclaration : HeaderRlpField → Decl (BitVec 64)
  | .uint => Guest.guestFn_hdr_uint_field
  | .bytes => Guest.guestFn_hdr_bytes_field
  | .raw => Guest.guestFn_hdr_raw_field

def headerRlpFieldTail (field : HeaderRlpField) : ProgHOL 64 :=
  statelessNext (structuralFunctionBody (headerRlpFieldDeclaration field))

def headerRlpFieldArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "i"),.const 16]]),
   .load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "i"),.const 16],.const 8])]

theorem source_header_rlp_field (field : HeaderRlpField) :
    sourceFunctionBody (headerRlpFieldDeclaration field) =
      .decCall (ofString "it") (.comb [.one,.one,.one,.one]) (ofString "rlp_item")
        headerRlpFieldArguments (headerRlpFieldTail field) := by
  cases field
  all_goals
    unfold sourceFunctionBody
    rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl

theorem header_rlp_field_tail_straight (field : HeaderRlpField) :
    straightLine (headerRlpFieldTail field) = true := by
  cases field <;> rfl

/-- The original raw/bytes/uint header-field helpers inherit the real item
parser's quadratic input bound; all following field checks are clock-free. -/
theorem runBounded_header_rlp_field {F : Type} (s : PanSemStateFiniteExact 64 F) (field : HeaderRlpField)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) headerRlpFieldArguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ s.clock) :
    RunBounded s (sourceFunctionBody (headerRlpFieldDeclaration field))
      (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633) := by
  rw [source_header_rlp_field]
  exact evaluate_rlpItem_declaration_bounded s (ofString "it") (headerRlpFieldTail field)
    (header_rlp_field_tail_straight field) headerRlpFieldArguments pointer length scratch frame ceiling inputLimit
    args noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget

#print axioms source_header_rlp_field
#print axioms header_rlp_field_tail_straight
#print axioms runBounded_header_rlp_field
end InitECandidate.Runtime
