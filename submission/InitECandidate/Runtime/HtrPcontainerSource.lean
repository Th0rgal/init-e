import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrPcontainerAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_htr_pcontainer)

def htrPcontainerMaskBody : ProgHOL 64 :=
  match htrPcontainerAt 6 with | .seq (.while _ body) _ => body | _ => .skip

def htrPcontainerMaskStore : ProgHOL 64 :=
  match htrPcontainerMaskBody with | .seq first _ => first | _ => .skip

theorem source_htrPcontainer_mark : htrPcontainerAt 0 =
    .decCall (ofString "mark") .one (ofString "heap_mark") [] (htrPcontainerAt 1) := by rfl

theorem source_htrPcontainer_alloc : htrPcontainerAt 1 =
    .decCall (ofString "tmp") .one (ofString "alloc") [.const 64] (htrPcontainerAt 2) := by rfl

theorem source_htrPcontainer_progressive : htrPcontainerAt 2 =
    .seq (.call (some (none,none)) (ofString "merkleize_progressive")
      [.var .local (ofString "ch"),.var .local (ofString "n"),.var .local (ofString "tmp")]) (htrPcontainerAt 3) := by rfl

theorem source_htrPcontainer_act : htrPcontainerAt 3 =
    .dec (ofString "act") .one (.op .add [.var .local (ofString "tmp"),.const 32]) (htrPcontainerAt 4) := by rfl

theorem source_htrPcontainer_zero : htrPcontainerAt 4 =
    .seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "act"),.const 32]) (htrPcontainerAt 5) := by rfl

theorem source_htrPcontainer_mask : htrPcontainerAt 5 =
    .dec (ofString "i") .one (.const 0)
      (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) htrPcontainerMaskBody)
        (htrPcontainerAt 7)) := by rfl

theorem source_htrPcontainer_mask_body : htrPcontainerMaskBody =
    .seq htrPcontainerMaskStore
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) := by rfl

theorem source_htrPcontainer_finish : htrPcontainerAt 7 =
    .seq (.call (some (none,none)) (ofString "sha256_pair")
      [.var .local (ofString "tmp"),.var .local (ofString "act"),.var .local (ofString "out")])
      (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
        (.return (.const 0))) := by rfl

#print axioms source_htrPcontainer_mark
#print axioms source_htrPcontainer_alloc
#print axioms source_htrPcontainer_progressive
#print axioms source_htrPcontainer_act
#print axioms source_htrPcontainer_zero
#print axioms source_htrPcontainer_mask
#print axioms source_htrPcontainer_mask_body
#print axioms source_htrPcontainer_finish
end InitECandidate.Runtime
