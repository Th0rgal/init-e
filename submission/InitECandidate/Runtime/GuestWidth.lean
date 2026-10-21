import InitECandidate.Runtime.CrepSharpWidth
import InitECandidate.Proofs.FrontendStages.Crep.FunctionsFacts
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-! Width certificate for the exact `pan_to_crep` input of the guest
(`Crep.inputFunctions`, 826 functions): every `dec`/`decCall` shape, parameter
and return shape is at most 21 words. One `decide_cbv` per function; the list
is peeled one element at a time. -/

/-- A declaration's declared shapes are at most 21 words. -/
def guestWidthDecl : DeclHOL 64 → Bool
  | .function function => widthProg function.body &&
      function.params.all (fun p => decide (sizeOfShapeHOL p.2 ≤ 21)) &&
      decide (sizeOfShapeHOL function.returnShape ≤ 21)
  | _ => true


/-! Production-carrier mirror, for bodies too deep for elaborator evaluation:
the kernel decides it directly on the pinned production declarations. -/

mutual
  def shapeSizeP : Flapjack.Shape → Nat
    | .one => 1
    | .comb fields => shapesSizeP fields
    | .named _ => 1
  def shapesSizeP : List Flapjack.Shape → Nat
    | [] => 0
    | shape :: shapes => shapeSizeP shape + shapesSizeP shapes
end

mutual
  theorem shapeSize_toHOL : ∀ shape : Flapjack.Shape, sizeOfShapeHOL (shapeToHOL shape) = shapeSizeP shape
    | .one => by simp [shapeToHOL, shapeSizeP]
    | .comb fields => by
      simp only [shapeToHOL, sizeOfShapeHOL_comb, shapeSizeP]
      exact shapesSize_toHOL fields
    | .named _ => by simp [shapeToHOL, shapeSizeP, sizeOfShapeHOL]
  theorem shapesSize_toHOL : ∀ shapes : List Flapjack.Shape,
      sizeOfShapesHOL (shapes.map shapeToHOL) = shapesSizeP shapes
    | [] => by simp [sizeOfShapesHOL, shapesSizeP]
    | shape :: shapes => by
      simp only [List.map_cons, sizeOfShapesHOL, shapesSizeP]
      rw [shapeSize_toHOL shape, shapesSize_toHOL shapes]
end

def widthProgP : Flapjack.Prog (BitVec 64) → Bool
  | .dec _ shape _ body => decide (shapeSizeP shape ≤ 21) && widthProgP body
  | .decCall _ shape _ _ continuation => decide (shapeSizeP shape ≤ 21) && widthProgP continuation
  | .seq first second => widthProgP first && widthProgP second
  | .ite _ yes no => widthProgP yes && widthProgP no
  | .while _ body => widthProgP body
  | .call (some (_, some (_, _, handler))) _ _ => widthProgP handler
  | _ => true

theorem widthProg_toHOL : ∀ p : Flapjack.Prog (BitVec 64), widthProg (progToHOL p) = widthProgP p
  | .dec _ shape _ body => by
    simp only [progToHOL, widthProg, widthProgP, shapeSize_toHOL, widthProg_toHOL body]
  | .decCall _ shape _ _ continuation => by
    simp only [progToHOL, widthProg, widthProgP, shapeSize_toHOL, widthProg_toHOL continuation]
  | .seq first second => by
    simp only [progToHOL, widthProg, widthProgP, widthProg_toHOL first, widthProg_toHOL second]
  | .ite _ yes no => by
    simp only [progToHOL, widthProg, widthProgP, widthProg_toHOL yes, widthProg_toHOL no]
  | .while _ body => by simp only [progToHOL, widthProg, widthProgP, widthProg_toHOL body]
  | .call none _ _ => by simp [progToHOL, widthProg, widthProgP]
  | .call (some (_, none)) _ _ => by simp [progToHOL, widthProg, widthProgP]
  | .call (some (_, some (_, _, handler))) _ _ => by
    simp only [progToHOL, widthProg, widthProgP, widthProg_toHOL handler]
  | .skip | .assign .. | .primitive .. | .store .. | .store32 .. | .storeByte .. | .break | .continue
  | .extCall .. | .raise .. | .return .. | .shMemLoad .. | .shMemStore .. | .tick | .annot .. => by
    simp [progToHOL, widthProg, widthProgP]

def widthDeclP : Flapjack.Decl (BitVec 64) → Bool
  | .function function => widthProgP function.body &&
      function.params.all (fun p => decide (shapeSizeP p.2 ≤ 21)) &&
      decide (shapeSizeP function.returnShape ≤ 21)
  | _ => true

theorem guestWidthDecl_toHOL (d : Flapjack.Decl (BitVec 64)) : guestWidthDecl (declToHOL d) = widthDeclP d := by
  cases d with
  | function f =>
    simp only [declToHOL, funDeclToHOL, guestWidthDecl, widthDeclP, widthProg_toHOL, shapeSize_toHOL,
      List.all_map, Function.comp_def, paramToHOL]
  | _ => simp [declToHOL, guestWidthDecl, widthDeclP]

theorem width_step {P : DeclHOL 64 → Prop} {a : DeclHOL 64} {t : List (DeclHOL 64)} (ha : P a)
    (ht : ∀ x ∈ t, P x) : ∀ x ∈ a :: t, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  · exact ht x hx

theorem guest_width_0 : guestWidthDecl InitECandidate.Proofs.FrontendStages.generatedMain = true := by decide_cbv
theorem guest_width_1 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput0 = true := by decide_cbv
theorem guest_width_2 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput4 = true := by decide_cbv
theorem guest_width_3 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput7 = true := by decide_cbv
theorem guest_width_4 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput8 = true := by decide_cbv
theorem guest_width_5 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput9 = true := by decide_cbv
theorem guest_width_6 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput10 = true := by decide_cbv
theorem guest_width_7 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput11 = true := by decide_cbv
theorem guest_width_8 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput12 = true := by decide_cbv
theorem guest_width_9 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput13 = true := by decide_cbv
theorem guest_width_10 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput14 = true := by decide_cbv
theorem guest_width_11 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput15 = true := by decide_cbv
theorem guest_width_12 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput16 = true := by decide_cbv
theorem guest_width_13 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput17 = true := by decide_cbv
theorem guest_width_14 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput18 = true := by decide_cbv
theorem guest_width_15 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput19 = true := by decide_cbv
theorem guest_width_16 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput20 = true := by decide_cbv
theorem guest_width_17 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput21 = true := by decide_cbv
theorem guest_width_18 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput22 = true := by decide_cbv
theorem guest_width_19 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput23 = true := by decide_cbv
theorem guest_width_20 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput24 = true := by decide_cbv
theorem guest_width_21 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput25 = true := by decide_cbv
theorem guest_width_22 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput26 = true := by decide_cbv
theorem guest_width_23 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput27 = true := by decide_cbv
theorem guest_width_24 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput28 = true := by decide_cbv
theorem guest_width_25 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput29 = true := by decide_cbv
theorem guest_width_26 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput30 = true := by decide_cbv
theorem guest_width_27 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput31 = true := by decide_cbv
theorem guest_width_28 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput32 = true := by decide_cbv
theorem guest_width_29 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput33 = true := by decide_cbv
theorem guest_width_30 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput34 = true := by decide_cbv
theorem guest_width_31 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput35 = true := by decide_cbv
theorem guest_width_32 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput36 = true := by decide_cbv
theorem guest_width_33 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput37 = true := by decide_cbv
theorem guest_width_34 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput39 = true := by decide_cbv
theorem guest_width_35 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput40 = true := by decide_cbv
theorem guest_width_36 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput41 = true := by decide_cbv
theorem guest_width_37 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput42 = true := by decide_cbv
theorem guest_width_38 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput43 = true := by decide_cbv
theorem guest_width_39 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput44 = true := by decide_cbv
theorem guest_width_40 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput45 = true := by decide_cbv
theorem guest_width_41 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput46 = true := by decide_cbv
theorem guest_width_42 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput47 = true := by decide_cbv
theorem guest_width_43 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput48 = true := by decide_cbv
theorem guest_width_44 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput49 = true := by decide_cbv
theorem guest_width_45 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput50 = true := by decide_cbv
theorem guest_width_46 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput51 = true := by decide_cbv
theorem guest_width_47 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput52 = true := by decide_cbv
theorem guest_width_48 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput53 = true := by decide_cbv
theorem guest_width_49 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput54 = true := by decide_cbv
theorem guest_width_50 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput55 = true := by decide_cbv
theorem guest_width_51 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput56 = true := by decide_cbv
theorem guest_width_52 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput57 = true := by decide_cbv
theorem guest_width_53 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput58 = true := by decide_cbv
theorem guest_width_54 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput59 = true := by decide_cbv
theorem guest_width_55 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput60 = true := by decide_cbv
theorem guest_width_56 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput61 = true := by decide_cbv
theorem guest_width_57 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput62 = true := by decide_cbv
theorem guest_width_58 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput63 = true := by decide_cbv
theorem guest_width_59 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput64 = true := by decide_cbv
theorem guest_width_60 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput65 = true := by decide_cbv
theorem guest_width_61 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput66 = true := by decide_cbv
theorem guest_width_62 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput67 = true := by decide_cbv
theorem guest_width_63 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput68 = true := by decide_cbv
theorem guest_width_64 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput69 = true := by decide_cbv
theorem guest_width_65 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput70 = true := by decide_cbv
theorem guest_width_66 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput71 = true := by decide_cbv
theorem guest_width_67 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput72 = true := by decide_cbv
theorem guest_width_68 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput73 = true := by decide_cbv
theorem guest_width_69 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput74 = true := by decide_cbv
theorem guest_width_70 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput75 = true := by decide_cbv
theorem guest_width_71 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput76 = true := by decide_cbv
theorem guest_width_72 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput77 = true := by decide_cbv
theorem guest_width_73 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput78 = true := by decide_cbv
theorem guest_width_74 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput79 = true := by decide_cbv
theorem guest_width_75 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput80 = true := by decide_cbv
theorem guest_width_76 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput81 = true := by decide_cbv
theorem guest_width_77 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput82 = true := by decide_cbv
theorem guest_width_78 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput83 = true := by decide_cbv
theorem guest_width_79 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput84 = true := by decide_cbv
theorem guest_width_80 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput85 = true := by decide_cbv
theorem guest_width_81 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput86 = true := by decide_cbv
theorem guest_width_82 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput87 = true := by decide_cbv
theorem guest_width_83 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput88 = true := by decide_cbv
theorem guest_width_84 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput89 = true := by decide_cbv
theorem guest_width_85 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput93 = true := by decide_cbv
theorem guest_width_86 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput94 = true := by decide_cbv
theorem guest_width_87 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput95 = true := by decide_cbv
theorem guest_width_88 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput96 = true := by decide_cbv
theorem guest_width_89 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput97 = true := by decide_cbv
theorem guest_width_90 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput98 = true := by decide_cbv
theorem guest_width_91 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput101 = true := by decide_cbv
theorem guest_width_92 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput102 = true := by decide_cbv
theorem guest_width_93 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput103 = true := by decide_cbv
theorem guest_width_94 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput104 = true := by decide_cbv
theorem guest_width_95 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput106 = true := by decide_cbv
theorem guest_width_96 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput107 = true := by decide_cbv
theorem guest_width_97 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput108 = true := by decide_cbv
theorem guest_width_98 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput109 = true := by decide_cbv
theorem guest_width_99 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput110 = true := by decide_cbv
theorem guest_width_100 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput111 = true := by decide_cbv
theorem guest_width_101 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput112 = true := by decide_cbv
theorem guest_width_102 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput113 = true := by decide_cbv
theorem guest_width_103 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput114 = true := by decide_cbv
theorem guest_width_104 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput115 = true := by decide_cbv
theorem guest_width_105 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput116 = true := by decide_cbv
theorem guest_width_106 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput117 = true := by decide_cbv
theorem guest_width_107 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput118 = true := by decide_cbv
theorem guest_width_108 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput119 = true := by decide_cbv
theorem guest_width_109 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput120 = true := by decide_cbv
theorem guest_width_110 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput121 = true := by decide_cbv
theorem guest_width_111 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput122 = true := by decide_cbv
theorem guest_width_112 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput123 = true := by decide_cbv
theorem guest_width_113 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput124 = true := by decide_cbv
theorem guest_width_114 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput125 = true := by decide_cbv
theorem guest_width_115 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput126 = true := by decide_cbv
theorem guest_width_116 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput127 = true := by decide_cbv
theorem guest_width_117 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput128 = true := by decide_cbv
theorem guest_width_118 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput129 = true := by decide_cbv
theorem guest_width_119 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput130 = true := by decide_cbv
theorem guest_width_120 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput131 = true := by decide_cbv
theorem guest_width_121 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput132 = true := by decide_cbv
theorem guest_width_122 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput133 = true := by decide_cbv
theorem guest_width_123 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput134 = true := by decide_cbv
theorem guest_width_124 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput135 = true := by decide_cbv
theorem guest_width_125 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput136 = true := by decide_cbv
theorem guest_width_126 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput137 = true := by decide_cbv
theorem guest_width_127 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput138 = true := by decide_cbv
theorem guest_width_128 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput139 = true := by decide_cbv
theorem guest_width_129 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput140 = true := by decide_cbv
theorem guest_width_130 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput141 = true := by decide_cbv
theorem guest_width_131 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput142 = true := by decide_cbv
theorem guest_width_132 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput143 = true := by decide_cbv
theorem guest_width_133 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput144 = true := by decide_cbv
theorem guest_width_134 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput145 = true := by decide_cbv
theorem guest_width_135 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput146 = true := by decide_cbv
theorem guest_width_136 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput148 = true := by decide_cbv
theorem guest_width_137 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput149 = true := by decide_cbv
theorem guest_width_138 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput150 = true := by decide_cbv
theorem guest_width_139 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput151 = true := by decide_cbv
theorem guest_width_140 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput152 = true := by decide_cbv
theorem guest_width_141 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput153 = true := by decide_cbv
theorem guest_width_142 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput154 = true := by decide_cbv
theorem guest_width_143 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput155 = true := by decide_cbv
theorem guest_width_144 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput156 = true := by decide_cbv
theorem guest_width_145 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput157 = true := by decide_cbv
theorem guest_width_146 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput158 = true := by decide_cbv
theorem guest_width_147 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput159 = true := by decide_cbv
theorem guest_width_148 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput160 = true := by decide_cbv
theorem guest_width_149 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput161 = true := by decide_cbv
theorem guest_width_150 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput162 = true := by decide_cbv
theorem guest_width_151 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput163 = true := by decide_cbv
theorem guest_width_152 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput164 = true := by decide_cbv
theorem guest_width_153 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput165 = true := by decide_cbv
theorem guest_width_154 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput166 = true := by decide_cbv
theorem guest_width_155 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput167 = true := by decide_cbv
theorem guest_width_156 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput168 = true := by decide_cbv
theorem guest_width_157 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput169 = true := by decide_cbv
theorem guest_width_158 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput170 = true := by decide_cbv
theorem guest_width_159 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput171 = true := by decide_cbv
theorem guest_width_160 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput172 = true := by decide_cbv
theorem guest_width_161 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput173 = true := by decide_cbv
theorem guest_width_162 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput174 = true := by decide_cbv
theorem guest_width_163 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput175 = true := by decide_cbv
theorem guest_width_164 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput176 = true := by decide_cbv
theorem guest_width_165 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput177 = true := by decide_cbv
theorem guest_width_166 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput178 = true := by decide_cbv
theorem guest_width_167 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput179 = true := by decide_cbv
theorem guest_width_168 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput180 = true := by decide_cbv
theorem guest_width_169 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput181 = true := by decide_cbv
theorem guest_width_170 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput182 = true := by decide_cbv
theorem guest_width_171 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput183 = true := by decide_cbv
theorem guest_width_172 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput184 = true := by decide_cbv
theorem guest_width_173 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput185 = true := by decide_cbv
theorem guest_width_174 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput186 = true := by decide_cbv
theorem guest_width_175 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput187 = true := by decide_cbv
theorem guest_width_176 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput192 = true := by
  rw [show InitECandidate.Proofs.FrontendStages.Declarations.globalOutput192 =
    declToHOL InitECandidate.Proofs.FrontendStages.Declarations.globalData192 from rfl, guestWidthDecl_toHOL]
  decide +kernel
theorem guest_width_177 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput193 = true := by decide_cbv
theorem guest_width_178 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput194 = true := by decide_cbv
theorem guest_width_179 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput195 = true := by decide_cbv
theorem guest_width_180 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput196 = true := by decide_cbv
theorem guest_width_181 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput197 = true := by decide_cbv
theorem guest_width_182 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput198 = true := by decide_cbv
theorem guest_width_183 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput199 = true := by decide_cbv
theorem guest_width_184 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput200 = true := by decide_cbv
theorem guest_width_185 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput201 = true := by decide_cbv
theorem guest_width_186 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput202 = true := by decide_cbv
theorem guest_width_187 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput203 = true := by decide_cbv
theorem guest_width_188 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput204 = true := by decide_cbv
theorem guest_width_189 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput205 = true := by decide_cbv
theorem guest_width_190 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput206 = true := by decide_cbv
theorem guest_width_191 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput207 = true := by decide_cbv
theorem guest_width_192 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput208 = true := by decide_cbv
theorem guest_width_193 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput209 = true := by decide_cbv
theorem guest_width_194 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput210 = true := by decide_cbv
theorem guest_width_195 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput211 = true := by decide_cbv
theorem guest_width_196 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput212 = true := by decide_cbv
theorem guest_width_197 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput213 = true := by decide_cbv
theorem guest_width_198 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput214 = true := by decide_cbv
theorem guest_width_199 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput215 = true := by decide_cbv
theorem guest_width_200 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput216 = true := by decide_cbv
theorem guest_width_201 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput217 = true := by decide_cbv
theorem guest_width_202 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput218 = true := by decide_cbv
theorem guest_width_203 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput219 = true := by decide_cbv
theorem guest_width_204 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput220 = true := by decide_cbv
theorem guest_width_205 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput221 = true := by decide_cbv
theorem guest_width_206 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput222 = true := by decide_cbv
theorem guest_width_207 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput225 = true := by decide_cbv
theorem guest_width_208 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput226 = true := by decide_cbv
theorem guest_width_209 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput227 = true := by decide_cbv
theorem guest_width_210 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput228 = true := by decide_cbv
theorem guest_width_211 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput229 = true := by decide_cbv
theorem guest_width_212 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput230 = true := by decide_cbv
theorem guest_width_213 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput231 = true := by decide_cbv
theorem guest_width_214 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput232 = true := by decide_cbv
theorem guest_width_215 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput233 = true := by decide_cbv
theorem guest_width_216 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput234 = true := by decide_cbv
theorem guest_width_217 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput235 = true := by decide_cbv
theorem guest_width_218 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput236 = true := by decide_cbv
theorem guest_width_219 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput237 = true := by decide_cbv
theorem guest_width_220 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput238 = true := by decide_cbv
theorem guest_width_221 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput239 = true := by decide_cbv
theorem guest_width_222 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput241 = true := by decide_cbv
theorem guest_width_223 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput242 = true := by decide_cbv
theorem guest_width_224 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput249 = true := by decide_cbv
theorem guest_width_225 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput250 = true := by decide_cbv
theorem guest_width_226 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput251 = true := by decide_cbv
theorem guest_width_227 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput252 = true := by decide_cbv
theorem guest_width_228 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput253 = true := by decide_cbv
theorem guest_width_229 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput254 = true := by decide_cbv
theorem guest_width_230 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput255 = true := by decide_cbv
theorem guest_width_231 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput256 = true := by decide_cbv
theorem guest_width_232 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput257 = true := by decide_cbv
theorem guest_width_233 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput258 = true := by decide_cbv
theorem guest_width_234 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput259 = true := by decide_cbv
theorem guest_width_235 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput260 = true := by decide_cbv
theorem guest_width_236 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput261 = true := by decide_cbv
theorem guest_width_237 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput262 = true := by decide_cbv
theorem guest_width_238 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput263 = true := by decide_cbv
theorem guest_width_239 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput264 = true := by decide_cbv
theorem guest_width_240 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput265 = true := by decide_cbv
theorem guest_width_241 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput266 = true := by decide_cbv
theorem guest_width_242 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput267 = true := by decide_cbv
theorem guest_width_243 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput268 = true := by decide_cbv
theorem guest_width_244 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput269 = true := by decide_cbv
theorem guest_width_245 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput270 = true := by decide_cbv
theorem guest_width_246 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput271 = true := by decide_cbv
theorem guest_width_247 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput272 = true := by decide_cbv
theorem guest_width_248 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput273 = true := by decide_cbv
theorem guest_width_249 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput274 = true := by decide_cbv
theorem guest_width_250 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput275 = true := by decide_cbv
theorem guest_width_251 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput276 = true := by decide_cbv
theorem guest_width_252 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput277 = true := by decide_cbv
theorem guest_width_253 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput278 = true := by decide_cbv
theorem guest_width_254 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput279 = true := by decide_cbv
theorem guest_width_255 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput280 = true := by decide_cbv
theorem guest_width_256 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput281 = true := by decide_cbv
theorem guest_width_257 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput282 = true := by decide_cbv
theorem guest_width_258 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput283 = true := by decide_cbv
theorem guest_width_259 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput284 = true := by decide_cbv
theorem guest_width_260 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput285 = true := by decide_cbv
theorem guest_width_261 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput286 = true := by decide_cbv
theorem guest_width_262 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput287 = true := by decide_cbv
theorem guest_width_263 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput288 = true := by decide_cbv
theorem guest_width_264 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput289 = true := by decide_cbv
theorem guest_width_265 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput290 = true := by decide_cbv
theorem guest_width_266 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput291 = true := by decide_cbv
theorem guest_width_267 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput292 = true := by decide_cbv
theorem guest_width_268 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput293 = true := by decide_cbv
theorem guest_width_269 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput294 = true := by decide_cbv
theorem guest_width_270 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput295 = true := by decide_cbv
theorem guest_width_271 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput296 = true := by decide_cbv
theorem guest_width_272 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput297 = true := by decide_cbv
theorem guest_width_273 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput299 = true := by decide_cbv
theorem guest_width_274 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput300 = true := by decide_cbv
theorem guest_width_275 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput301 = true := by decide_cbv
theorem guest_width_276 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput302 = true := by decide_cbv
theorem guest_width_277 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput303 = true := by decide_cbv
theorem guest_width_278 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput304 = true := by decide_cbv
theorem guest_width_279 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput305 = true := by decide_cbv
theorem guest_width_280 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput306 = true := by decide_cbv
theorem guest_width_281 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput307 = true := by decide_cbv
theorem guest_width_282 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput308 = true := by decide_cbv
theorem guest_width_283 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput309 = true := by decide_cbv
theorem guest_width_284 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput310 = true := by decide_cbv
theorem guest_width_285 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput311 = true := by decide_cbv
theorem guest_width_286 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput312 = true := by decide_cbv
theorem guest_width_287 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput313 = true := by decide_cbv
theorem guest_width_288 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput314 = true := by decide_cbv
theorem guest_width_289 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput315 = true := by decide_cbv
theorem guest_width_290 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput316 = true := by decide_cbv
theorem guest_width_291 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput317 = true := by decide_cbv
theorem guest_width_292 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput318 = true := by decide_cbv
theorem guest_width_293 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput319 = true := by decide_cbv
theorem guest_width_294 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput320 = true := by decide_cbv
theorem guest_width_295 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput321 = true := by decide_cbv
theorem guest_width_296 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput322 = true := by decide_cbv
theorem guest_width_297 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput323 = true := by decide_cbv
theorem guest_width_298 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput324 = true := by decide_cbv
theorem guest_width_299 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput325 = true := by decide_cbv
theorem guest_width_300 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput326 = true := by decide_cbv
theorem guest_width_301 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput327 = true := by decide_cbv
theorem guest_width_302 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput328 = true := by decide_cbv
theorem guest_width_303 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput329 = true := by decide_cbv
theorem guest_width_304 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput330 = true := by decide_cbv
theorem guest_width_305 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput331 = true := by decide_cbv
theorem guest_width_306 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput332 = true := by decide_cbv
theorem guest_width_307 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput333 = true := by decide_cbv
theorem guest_width_308 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput334 = true := by decide_cbv
theorem guest_width_309 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput335 = true := by decide_cbv
theorem guest_width_310 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput336 = true := by decide_cbv
theorem guest_width_311 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput337 = true := by decide_cbv
theorem guest_width_312 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput338 = true := by decide_cbv
theorem guest_width_313 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput339 = true := by decide_cbv
theorem guest_width_314 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput340 = true := by decide_cbv
theorem guest_width_315 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput341 = true := by decide_cbv
theorem guest_width_316 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput342 = true := by decide_cbv
theorem guest_width_317 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput343 = true := by decide_cbv
theorem guest_width_318 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput344 = true := by decide_cbv
theorem guest_width_319 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput345 = true := by decide_cbv
theorem guest_width_320 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput346 = true := by decide_cbv
theorem guest_width_321 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput347 = true := by decide_cbv
theorem guest_width_322 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput348 = true := by decide_cbv
theorem guest_width_323 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput349 = true := by decide_cbv
theorem guest_width_324 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput357 = true := by decide_cbv
theorem guest_width_325 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput358 = true := by decide_cbv
theorem guest_width_326 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput359 = true := by decide_cbv
theorem guest_width_327 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput360 = true := by decide_cbv
theorem guest_width_328 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput361 = true := by decide_cbv
theorem guest_width_329 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput362 = true := by decide_cbv
theorem guest_width_330 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput363 = true := by decide_cbv
theorem guest_width_331 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput364 = true := by decide_cbv
theorem guest_width_332 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput365 = true := by decide_cbv
theorem guest_width_333 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput366 = true := by decide_cbv
theorem guest_width_334 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput367 = true := by decide_cbv
theorem guest_width_335 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput368 = true := by decide_cbv
theorem guest_width_336 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput369 = true := by decide_cbv
theorem guest_width_337 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput370 = true := by decide_cbv
theorem guest_width_338 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput371 = true := by decide_cbv
theorem guest_width_339 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput372 = true := by decide_cbv
theorem guest_width_340 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput373 = true := by decide_cbv
theorem guest_width_341 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput374 = true := by decide_cbv
theorem guest_width_342 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput375 = true := by decide_cbv
theorem guest_width_343 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput376 = true := by decide_cbv
theorem guest_width_344 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput377 = true := by decide_cbv
theorem guest_width_345 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput378 = true := by decide_cbv
theorem guest_width_346 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput379 = true := by decide_cbv
theorem guest_width_347 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput380 = true := by decide_cbv
theorem guest_width_348 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput381 = true := by decide_cbv
theorem guest_width_349 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput382 = true := by decide_cbv
theorem guest_width_350 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput383 = true := by decide_cbv
theorem guest_width_351 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput384 = true := by decide_cbv
theorem guest_width_352 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput385 = true := by decide_cbv
theorem guest_width_353 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput386 = true := by decide_cbv
theorem guest_width_354 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput387 = true := by decide_cbv
theorem guest_width_355 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput388 = true := by decide_cbv
theorem guest_width_356 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput389 = true := by decide_cbv
theorem guest_width_357 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput390 = true := by decide_cbv
theorem guest_width_358 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput391 = true := by decide_cbv
theorem guest_width_359 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput392 = true := by decide_cbv
theorem guest_width_360 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput393 = true := by decide_cbv
theorem guest_width_361 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput394 = true := by decide_cbv
theorem guest_width_362 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput395 = true := by decide_cbv
theorem guest_width_363 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput396 = true := by decide_cbv
theorem guest_width_364 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput397 = true := by decide_cbv
theorem guest_width_365 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput398 = true := by decide_cbv
theorem guest_width_366 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput399 = true := by decide_cbv
theorem guest_width_367 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput400 = true := by decide_cbv
theorem guest_width_368 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput401 = true := by decide_cbv
theorem guest_width_369 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput402 = true := by decide_cbv
theorem guest_width_370 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput403 = true := by decide_cbv
theorem guest_width_371 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput404 = true := by decide_cbv
theorem guest_width_372 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput405 = true := by decide_cbv
theorem guest_width_373 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput411 = true := by decide_cbv
theorem guest_width_374 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput412 = true := by decide_cbv
theorem guest_width_375 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput413 = true := by decide_cbv
theorem guest_width_376 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput414 = true := by decide_cbv
theorem guest_width_377 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput415 = true := by decide_cbv
theorem guest_width_378 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput416 = true := by decide_cbv
theorem guest_width_379 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput417 = true := by decide_cbv
theorem guest_width_380 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput418 = true := by decide_cbv
theorem guest_width_381 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput419 = true := by decide_cbv
theorem guest_width_382 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput420 = true := by decide_cbv
theorem guest_width_383 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput421 = true := by decide_cbv
theorem guest_width_384 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput422 = true := by decide_cbv
theorem guest_width_385 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput423 = true := by decide_cbv
theorem guest_width_386 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput424 = true := by decide_cbv
theorem guest_width_387 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput425 = true := by decide_cbv
theorem guest_width_388 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput426 = true := by decide_cbv
theorem guest_width_389 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput427 = true := by decide_cbv
theorem guest_width_390 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput428 = true := by decide_cbv
theorem guest_width_391 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput429 = true := by decide_cbv
theorem guest_width_392 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput430 = true := by decide_cbv
theorem guest_width_393 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput431 = true := by decide_cbv
theorem guest_width_394 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput432 = true := by decide_cbv
theorem guest_width_395 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput433 = true := by decide_cbv
theorem guest_width_396 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput434 = true := by decide_cbv
theorem guest_width_397 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput435 = true := by decide_cbv
theorem guest_width_398 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput436 = true := by decide_cbv
theorem guest_width_399 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput437 = true := by decide_cbv
theorem guest_width_400 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput443 = true := by decide_cbv
theorem guest_width_401 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput444 = true := by decide_cbv
theorem guest_width_402 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput445 = true := by decide_cbv
theorem guest_width_403 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput446 = true := by decide_cbv
theorem guest_width_404 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput447 = true := by decide_cbv
theorem guest_width_405 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput448 = true := by decide_cbv
theorem guest_width_406 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput449 = true := by decide_cbv
theorem guest_width_407 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput450 = true := by decide_cbv
theorem guest_width_408 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput451 = true := by decide_cbv
theorem guest_width_409 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput452 = true := by decide_cbv
theorem guest_width_410 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput453 = true := by decide_cbv
theorem guest_width_411 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput454 = true := by decide_cbv
theorem guest_width_412 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput455 = true := by decide_cbv
theorem guest_width_413 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput456 = true := by decide_cbv
theorem guest_width_414 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput457 = true := by decide_cbv
theorem guest_width_415 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput458 = true := by decide_cbv
theorem guest_width_416 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput459 = true := by decide_cbv
theorem guest_width_417 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput460 = true := by decide_cbv
theorem guest_width_418 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput461 = true := by decide_cbv
theorem guest_width_419 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput462 = true := by decide_cbv
theorem guest_width_420 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput463 = true := by decide_cbv
theorem guest_width_421 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput464 = true := by decide_cbv
theorem guest_width_422 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput465 = true := by decide_cbv
theorem guest_width_423 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput466 = true := by decide_cbv
theorem guest_width_424 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput467 = true := by decide_cbv
theorem guest_width_425 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput468 = true := by decide_cbv
theorem guest_width_426 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput469 = true := by decide_cbv
theorem guest_width_427 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput470 = true := by decide_cbv
theorem guest_width_428 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput471 = true := by decide_cbv
theorem guest_width_429 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput472 = true := by decide_cbv
theorem guest_width_430 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput473 = true := by decide_cbv
theorem guest_width_431 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput474 = true := by decide_cbv
theorem guest_width_432 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput475 = true := by decide_cbv
theorem guest_width_433 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput476 = true := by decide_cbv
theorem guest_width_434 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput477 = true := by decide_cbv
theorem guest_width_435 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput478 = true := by decide_cbv
theorem guest_width_436 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput479 = true := by decide_cbv
theorem guest_width_437 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput480 = true := by decide_cbv
theorem guest_width_438 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput481 = true := by decide_cbv
theorem guest_width_439 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput482 = true := by decide_cbv
theorem guest_width_440 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput483 = true := by decide_cbv
theorem guest_width_441 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput484 = true := by decide_cbv
theorem guest_width_442 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput485 = true := by decide_cbv
theorem guest_width_443 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput486 = true := by decide_cbv
theorem guest_width_444 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput487 = true := by decide_cbv
theorem guest_width_445 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput488 = true := by decide_cbv
theorem guest_width_446 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput489 = true := by decide_cbv
theorem guest_width_447 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput490 = true := by decide_cbv
theorem guest_width_448 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput491 = true := by decide_cbv
theorem guest_width_449 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput492 = true := by decide_cbv
theorem guest_width_450 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput493 = true := by decide_cbv
theorem guest_width_451 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput494 = true := by decide_cbv
theorem guest_width_452 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput495 = true := by decide_cbv
theorem guest_width_453 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput496 = true := by decide_cbv
theorem guest_width_454 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput497 = true := by decide_cbv
theorem guest_width_455 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput498 = true := by decide_cbv
theorem guest_width_456 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput499 = true := by decide_cbv
theorem guest_width_457 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput500 = true := by decide_cbv
theorem guest_width_458 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput501 = true := by decide_cbv
theorem guest_width_459 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput502 = true := by decide_cbv
theorem guest_width_460 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput503 = true := by decide_cbv
theorem guest_width_461 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput504 = true := by decide_cbv
theorem guest_width_462 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput505 = true := by decide_cbv
theorem guest_width_463 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput506 = true := by decide_cbv
theorem guest_width_464 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput507 = true := by decide_cbv
theorem guest_width_465 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput508 = true := by decide_cbv
theorem guest_width_466 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput509 = true := by decide_cbv
theorem guest_width_467 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput510 = true := by decide_cbv
theorem guest_width_468 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput511 = true := by decide_cbv
theorem guest_width_469 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput512 = true := by decide_cbv
theorem guest_width_470 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput513 = true := by decide_cbv
theorem guest_width_471 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput514 = true := by decide_cbv
theorem guest_width_472 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput515 = true := by decide_cbv
theorem guest_width_473 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput516 = true := by decide_cbv
theorem guest_width_474 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput517 = true := by decide_cbv
theorem guest_width_475 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput518 = true := by decide_cbv
theorem guest_width_476 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput519 = true := by decide_cbv
theorem guest_width_477 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput520 = true := by decide_cbv
theorem guest_width_478 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput521 = true := by decide_cbv
theorem guest_width_479 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput522 = true := by decide_cbv
theorem guest_width_480 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput523 = true := by decide_cbv
theorem guest_width_481 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput524 = true := by decide_cbv
theorem guest_width_482 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput525 = true := by decide_cbv
theorem guest_width_483 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput526 = true := by decide_cbv
theorem guest_width_484 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput527 = true := by decide_cbv
theorem guest_width_485 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput528 = true := by decide_cbv
theorem guest_width_486 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput529 = true := by decide_cbv
theorem guest_width_487 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput530 = true := by decide_cbv
theorem guest_width_488 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput531 = true := by decide_cbv
theorem guest_width_489 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput532 = true := by decide_cbv
theorem guest_width_490 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput533 = true := by decide_cbv
theorem guest_width_491 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput534 = true := by decide_cbv
theorem guest_width_492 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput535 = true := by decide_cbv
theorem guest_width_493 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput536 = true := by decide_cbv
theorem guest_width_494 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput537 = true := by decide_cbv
theorem guest_width_495 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput538 = true := by decide_cbv
theorem guest_width_496 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput539 = true := by decide_cbv
theorem guest_width_497 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput540 = true := by decide_cbv
theorem guest_width_498 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput541 = true := by decide_cbv
theorem guest_width_499 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput542 = true := by decide_cbv
theorem guest_width_500 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput543 = true := by decide_cbv
theorem guest_width_501 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput544 = true := by decide_cbv
theorem guest_width_502 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput545 = true := by decide_cbv
theorem guest_width_503 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput546 = true := by decide_cbv
theorem guest_width_504 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput547 = true := by decide_cbv
theorem guest_width_505 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput548 = true := by decide_cbv
theorem guest_width_506 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput549 = true := by decide_cbv
theorem guest_width_507 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput550 = true := by decide_cbv
theorem guest_width_508 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput551 = true := by decide_cbv
theorem guest_width_509 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput552 = true := by decide_cbv
theorem guest_width_510 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput553 = true := by decide_cbv
theorem guest_width_511 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput554 = true := by decide_cbv
theorem guest_width_512 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput555 = true := by decide_cbv
theorem guest_width_513 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput556 = true := by decide_cbv
theorem guest_width_514 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput557 = true := by decide_cbv
theorem guest_width_515 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput558 = true := by decide_cbv
theorem guest_width_516 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput559 = true := by decide_cbv
theorem guest_width_517 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput560 = true := by decide_cbv
theorem guest_width_518 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput561 = true := by decide_cbv
theorem guest_width_519 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput562 = true := by decide_cbv
theorem guest_width_520 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput563 = true := by decide_cbv
theorem guest_width_521 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput564 = true := by decide_cbv
theorem guest_width_522 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput569 = true := by decide_cbv
theorem guest_width_523 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput570 = true := by decide_cbv
theorem guest_width_524 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput571 = true := by decide_cbv
theorem guest_width_525 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput572 = true := by decide_cbv
theorem guest_width_526 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput573 = true := by decide_cbv
theorem guest_width_527 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput574 = true := by decide_cbv
theorem guest_width_528 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput575 = true := by decide_cbv
theorem guest_width_529 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput576 = true := by decide_cbv
theorem guest_width_530 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput577 = true := by decide_cbv
theorem guest_width_531 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput578 = true := by decide_cbv
theorem guest_width_532 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput579 = true := by decide_cbv
theorem guest_width_533 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput580 = true := by decide_cbv
theorem guest_width_534 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput581 = true := by decide_cbv
theorem guest_width_535 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput582 = true := by decide_cbv
theorem guest_width_536 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput583 = true := by decide_cbv
theorem guest_width_537 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput584 = true := by decide_cbv
theorem guest_width_538 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput585 = true := by decide_cbv
theorem guest_width_539 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput586 = true := by decide_cbv
theorem guest_width_540 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput587 = true := by decide_cbv
theorem guest_width_541 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput588 = true := by decide_cbv
theorem guest_width_542 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput589 = true := by decide_cbv
theorem guest_width_543 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput590 = true := by decide_cbv
theorem guest_width_544 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput591 = true := by decide_cbv
theorem guest_width_545 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput592 = true := by decide_cbv
theorem guest_width_546 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput593 = true := by decide_cbv
theorem guest_width_547 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput594 = true := by decide_cbv
theorem guest_width_548 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput595 = true := by decide_cbv
theorem guest_width_549 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput596 = true := by decide_cbv
theorem guest_width_550 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput597 = true := by decide_cbv
theorem guest_width_551 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput598 = true := by decide_cbv
theorem guest_width_552 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput599 = true := by decide_cbv
theorem guest_width_553 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput600 = true := by decide_cbv
theorem guest_width_554 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput601 = true := by decide_cbv
theorem guest_width_555 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput602 = true := by decide_cbv
theorem guest_width_556 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput603 = true := by decide_cbv
theorem guest_width_557 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput604 = true := by decide_cbv
theorem guest_width_558 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput605 = true := by decide_cbv
theorem guest_width_559 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput606 = true := by decide_cbv
theorem guest_width_560 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput607 = true := by decide_cbv
theorem guest_width_561 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput608 = true := by decide_cbv
theorem guest_width_562 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput609 = true := by decide_cbv
theorem guest_width_563 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput610 = true := by decide_cbv
theorem guest_width_564 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput615 = true := by decide_cbv
theorem guest_width_565 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput616 = true := by decide_cbv
theorem guest_width_566 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput617 = true := by decide_cbv
theorem guest_width_567 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput618 = true := by decide_cbv
theorem guest_width_568 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput619 = true := by decide_cbv
theorem guest_width_569 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput620 = true := by decide_cbv
theorem guest_width_570 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput626 = true := by decide_cbv
theorem guest_width_571 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput627 = true := by decide_cbv
theorem guest_width_572 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput628 = true := by decide_cbv
theorem guest_width_573 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput629 = true := by decide_cbv
theorem guest_width_574 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput630 = true := by decide_cbv
theorem guest_width_575 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput631 = true := by decide_cbv
theorem guest_width_576 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput632 = true := by decide_cbv
theorem guest_width_577 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput633 = true := by decide_cbv
theorem guest_width_578 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput634 = true := by decide_cbv
theorem guest_width_579 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput635 = true := by decide_cbv
theorem guest_width_580 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput636 = true := by decide_cbv
theorem guest_width_581 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput637 = true := by decide_cbv
theorem guest_width_582 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput638 = true := by
  rw [show InitECandidate.Proofs.FrontendStages.Declarations.globalOutput638 =
    declToHOL InitECandidate.Proofs.FrontendStages.Declarations.globalData638 from rfl, guestWidthDecl_toHOL]
  decide +kernel
theorem guest_width_583 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput639 = true := by
  rw [show InitECandidate.Proofs.FrontendStages.Declarations.globalOutput639 =
    declToHOL InitECandidate.Proofs.FrontendStages.Declarations.globalData639 from rfl, guestWidthDecl_toHOL]
  decide +kernel
theorem guest_width_584 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput640 = true := by decide_cbv
theorem guest_width_585 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput641 = true := by decide_cbv
theorem guest_width_586 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput642 = true := by decide_cbv
theorem guest_width_587 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput643 = true := by decide_cbv
theorem guest_width_588 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput644 = true := by decide_cbv
theorem guest_width_589 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput645 = true := by decide_cbv
theorem guest_width_590 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput646 = true := by decide_cbv
theorem guest_width_591 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput647 = true := by decide_cbv
theorem guest_width_592 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput648 = true := by decide_cbv
theorem guest_width_593 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput649 = true := by decide_cbv
theorem guest_width_594 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput665 = true := by decide_cbv
theorem guest_width_595 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput666 = true := by decide_cbv
theorem guest_width_596 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput667 = true := by decide_cbv
theorem guest_width_597 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput668 = true := by decide_cbv
theorem guest_width_598 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput669 = true := by decide_cbv
theorem guest_width_599 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput670 = true := by decide_cbv
theorem guest_width_600 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput671 = true := by decide_cbv
theorem guest_width_601 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput672 = true := by decide_cbv
theorem guest_width_602 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput673 = true := by decide_cbv
theorem guest_width_603 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput674 = true := by decide_cbv
theorem guest_width_604 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput675 = true := by decide_cbv
theorem guest_width_605 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput676 = true := by decide_cbv
theorem guest_width_606 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput677 = true := by decide_cbv
theorem guest_width_607 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput678 = true := by decide_cbv
theorem guest_width_608 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput679 = true := by decide_cbv
theorem guest_width_609 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput680 = true := by decide_cbv
theorem guest_width_610 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput681 = true := by decide_cbv
theorem guest_width_611 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput682 = true := by decide_cbv
theorem guest_width_612 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput683 = true := by decide_cbv
theorem guest_width_613 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput684 = true := by decide_cbv
theorem guest_width_614 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput685 = true := by decide_cbv
theorem guest_width_615 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput686 = true := by decide_cbv
theorem guest_width_616 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput687 = true := by decide_cbv
theorem guest_width_617 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput688 = true := by decide_cbv
theorem guest_width_618 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput689 = true := by decide_cbv
theorem guest_width_619 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput690 = true := by decide_cbv
theorem guest_width_620 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput691 = true := by decide_cbv
theorem guest_width_621 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput692 = true := by decide_cbv
theorem guest_width_622 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput693 = true := by decide_cbv
theorem guest_width_623 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput694 = true := by decide_cbv
theorem guest_width_624 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput695 = true := by decide_cbv
theorem guest_width_625 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput696 = true := by decide_cbv
theorem guest_width_626 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput697 = true := by decide_cbv
theorem guest_width_627 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput698 = true := by decide_cbv
theorem guest_width_628 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput699 = true := by decide_cbv
theorem guest_width_629 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput700 = true := by decide_cbv
theorem guest_width_630 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput701 = true := by decide_cbv
theorem guest_width_631 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput702 = true := by decide_cbv
theorem guest_width_632 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput703 = true := by decide_cbv
theorem guest_width_633 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput704 = true := by decide_cbv
theorem guest_width_634 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput705 = true := by decide_cbv
theorem guest_width_635 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput706 = true := by decide_cbv
theorem guest_width_636 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput707 = true := by decide_cbv
theorem guest_width_637 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput708 = true := by decide_cbv
theorem guest_width_638 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput709 = true := by decide_cbv
theorem guest_width_639 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput710 = true := by decide_cbv
theorem guest_width_640 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput711 = true := by decide_cbv
theorem guest_width_641 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput712 = true := by decide_cbv
theorem guest_width_642 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput713 = true := by decide_cbv
theorem guest_width_643 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput714 = true := by decide_cbv
theorem guest_width_644 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput715 = true := by decide_cbv
theorem guest_width_645 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput716 = true := by decide_cbv
theorem guest_width_646 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput717 = true := by decide_cbv
theorem guest_width_647 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput718 = true := by decide_cbv
theorem guest_width_648 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput719 = true := by decide_cbv
theorem guest_width_649 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput721 = true := by
  rw [show InitECandidate.Proofs.FrontendStages.Declarations.globalOutput721 =
    declToHOL InitECandidate.Proofs.FrontendStages.Declarations.globalData721 from rfl, guestWidthDecl_toHOL]
  decide +kernel
theorem guest_width_650 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput722 = true := by decide_cbv
theorem guest_width_651 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput723 = true := by decide_cbv
theorem guest_width_652 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput724 = true := by decide_cbv
theorem guest_width_653 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput725 = true := by decide_cbv
theorem guest_width_654 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput726 = true := by decide_cbv
theorem guest_width_655 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput727 = true := by decide_cbv
theorem guest_width_656 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput728 = true := by decide_cbv
theorem guest_width_657 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput729 = true := by decide_cbv
theorem guest_width_658 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput730 = true := by decide_cbv
theorem guest_width_659 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput736 = true := by decide_cbv
theorem guest_width_660 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput737 = true := by decide_cbv
theorem guest_width_661 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput738 = true := by decide_cbv
theorem guest_width_662 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput739 = true := by decide_cbv
theorem guest_width_663 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput740 = true := by decide_cbv
theorem guest_width_664 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput741 = true := by decide_cbv
theorem guest_width_665 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput742 = true := by decide_cbv
theorem guest_width_666 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput743 = true := by decide_cbv
theorem guest_width_667 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput744 = true := by decide_cbv
theorem guest_width_668 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput745 = true := by decide_cbv
theorem guest_width_669 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput746 = true := by decide_cbv
theorem guest_width_670 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput747 = true := by decide_cbv
theorem guest_width_671 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput748 = true := by decide_cbv
theorem guest_width_672 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput749 = true := by decide_cbv
theorem guest_width_673 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput750 = true := by decide_cbv
theorem guest_width_674 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput751 = true := by decide_cbv
theorem guest_width_675 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput752 = true := by decide_cbv
theorem guest_width_676 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput753 = true := by decide_cbv
theorem guest_width_677 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput754 = true := by decide_cbv
theorem guest_width_678 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput755 = true := by decide_cbv
theorem guest_width_679 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput756 = true := by decide_cbv
theorem guest_width_680 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput760 = true := by decide_cbv
theorem guest_width_681 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput761 = true := by decide_cbv
theorem guest_width_682 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput762 = true := by decide_cbv
theorem guest_width_683 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput763 = true := by decide_cbv
theorem guest_width_684 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput764 = true := by decide_cbv
theorem guest_width_685 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput765 = true := by decide_cbv
theorem guest_width_686 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput766 = true := by decide_cbv
theorem guest_width_687 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput767 = true := by decide_cbv
theorem guest_width_688 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput768 = true := by decide_cbv
theorem guest_width_689 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput769 = true := by decide_cbv
theorem guest_width_690 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput770 = true := by decide_cbv
theorem guest_width_691 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput771 = true := by decide_cbv
theorem guest_width_692 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput772 = true := by decide_cbv
theorem guest_width_693 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput773 = true := by decide_cbv
theorem guest_width_694 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput774 = true := by decide_cbv
theorem guest_width_695 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput775 = true := by decide_cbv
theorem guest_width_696 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput776 = true := by decide_cbv
theorem guest_width_697 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput777 = true := by decide_cbv
theorem guest_width_698 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput778 = true := by decide_cbv
theorem guest_width_699 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput779 = true := by decide_cbv
theorem guest_width_700 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput780 = true := by decide_cbv
theorem guest_width_701 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput781 = true := by decide_cbv
theorem guest_width_702 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput782 = true := by decide_cbv
theorem guest_width_703 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput783 = true := by decide_cbv
theorem guest_width_704 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput784 = true := by decide_cbv
theorem guest_width_705 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput785 = true := by decide_cbv
theorem guest_width_706 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput786 = true := by decide_cbv
theorem guest_width_707 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput787 = true := by decide_cbv
theorem guest_width_708 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput788 = true := by decide_cbv
theorem guest_width_709 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput789 = true := by decide_cbv
theorem guest_width_710 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput790 = true := by decide_cbv
theorem guest_width_711 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput791 = true := by decide_cbv
theorem guest_width_712 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput792 = true := by decide_cbv
theorem guest_width_713 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput796 = true := by decide_cbv
theorem guest_width_714 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput797 = true := by decide_cbv
theorem guest_width_715 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput798 = true := by decide_cbv
theorem guest_width_716 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput799 = true := by decide_cbv
theorem guest_width_717 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput800 = true := by decide_cbv
theorem guest_width_718 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput801 = true := by decide_cbv
theorem guest_width_719 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput802 = true := by decide_cbv
theorem guest_width_720 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput803 = true := by decide_cbv
theorem guest_width_721 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput804 = true := by decide_cbv
theorem guest_width_722 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput805 = true := by decide_cbv
theorem guest_width_723 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput806 = true := by decide_cbv
theorem guest_width_724 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput807 = true := by decide_cbv
theorem guest_width_725 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput808 = true := by decide_cbv
theorem guest_width_726 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput809 = true := by decide_cbv
theorem guest_width_727 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput810 = true := by decide_cbv
theorem guest_width_728 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput811 = true := by decide_cbv
theorem guest_width_729 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput812 = true := by decide_cbv
theorem guest_width_730 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput813 = true := by decide_cbv
theorem guest_width_731 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput814 = true := by decide_cbv
theorem guest_width_732 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput815 = true := by decide_cbv
theorem guest_width_733 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput816 = true := by decide_cbv
theorem guest_width_734 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput817 = true := by decide_cbv
theorem guest_width_735 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput818 = true := by decide_cbv
theorem guest_width_736 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput819 = true := by decide_cbv
theorem guest_width_737 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput820 = true := by decide_cbv
theorem guest_width_738 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput821 = true := by decide_cbv
theorem guest_width_739 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput822 = true := by decide_cbv
theorem guest_width_740 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput823 = true := by decide_cbv
theorem guest_width_741 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput824 = true := by decide_cbv
theorem guest_width_742 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput825 = true := by decide_cbv
theorem guest_width_743 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput826 = true := by decide_cbv
theorem guest_width_744 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput827 = true := by decide_cbv
theorem guest_width_745 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput828 = true := by decide_cbv
theorem guest_width_746 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput829 = true := by decide_cbv
theorem guest_width_747 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput830 = true := by decide_cbv
theorem guest_width_748 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput831 = true := by decide_cbv
theorem guest_width_749 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput832 = true := by decide_cbv
theorem guest_width_750 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput833 = true := by decide_cbv
theorem guest_width_751 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput834 = true := by decide_cbv
theorem guest_width_752 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput835 = true := by decide_cbv
theorem guest_width_753 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput836 = true := by decide_cbv
theorem guest_width_754 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput837 = true := by decide_cbv
theorem guest_width_755 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput838 = true := by decide_cbv
theorem guest_width_756 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput839 = true := by decide_cbv
theorem guest_width_757 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput840 = true := by decide_cbv
theorem guest_width_758 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput841 = true := by decide_cbv
theorem guest_width_759 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput842 = true := by decide_cbv
theorem guest_width_760 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput843 = true := by decide_cbv
theorem guest_width_761 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput844 = true := by decide_cbv
theorem guest_width_762 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput845 = true := by decide_cbv
theorem guest_width_763 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput846 = true := by decide_cbv
theorem guest_width_764 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput847 = true := by decide_cbv
theorem guest_width_765 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput848 = true := by decide_cbv
theorem guest_width_766 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput850 = true := by
  rw [show InitECandidate.Proofs.FrontendStages.Declarations.globalOutput850 =
    declToHOL InitECandidate.Proofs.FrontendStages.Declarations.globalData850 from rfl, guestWidthDecl_toHOL]
  decide +kernel
theorem guest_width_767 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput851 = true := by decide_cbv
theorem guest_width_768 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput852 = true := by decide_cbv
theorem guest_width_769 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput853 = true := by decide_cbv
theorem guest_width_770 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput854 = true := by decide_cbv
theorem guest_width_771 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput855 = true := by decide_cbv
theorem guest_width_772 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput856 = true := by decide_cbv
theorem guest_width_773 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput857 = true := by decide_cbv
theorem guest_width_774 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput858 = true := by decide_cbv
theorem guest_width_775 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput859 = true := by decide_cbv
theorem guest_width_776 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput860 = true := by decide_cbv
theorem guest_width_777 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput861 = true := by decide_cbv
theorem guest_width_778 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput862 = true := by decide_cbv
theorem guest_width_779 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput863 = true := by decide_cbv
theorem guest_width_780 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput864 = true := by decide_cbv
theorem guest_width_781 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput865 = true := by decide_cbv
theorem guest_width_782 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput866 = true := by decide_cbv
theorem guest_width_783 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput867 = true := by decide_cbv
theorem guest_width_784 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput868 = true := by decide_cbv
theorem guest_width_785 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput869 = true := by decide_cbv
theorem guest_width_786 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput870 = true := by decide_cbv
theorem guest_width_787 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput871 = true := by decide_cbv
theorem guest_width_788 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput872 = true := by decide_cbv
theorem guest_width_789 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput873 = true := by decide_cbv
theorem guest_width_790 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput874 = true := by decide_cbv
theorem guest_width_791 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput875 = true := by decide_cbv
theorem guest_width_792 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput876 = true := by decide_cbv
theorem guest_width_793 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput877 = true := by decide_cbv
theorem guest_width_794 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput878 = true := by decide_cbv
theorem guest_width_795 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput879 = true := by decide_cbv
theorem guest_width_796 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput880 = true := by decide_cbv
theorem guest_width_797 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput881 = true := by decide_cbv
theorem guest_width_798 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput882 = true := by decide_cbv
theorem guest_width_799 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput899 = true := by decide_cbv
theorem guest_width_800 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput900 = true := by decide_cbv
theorem guest_width_801 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput901 = true := by decide_cbv
theorem guest_width_802 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput903 = true := by decide_cbv
theorem guest_width_803 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput904 = true := by decide_cbv
theorem guest_width_804 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput905 = true := by decide_cbv
theorem guest_width_805 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput906 = true := by decide_cbv
theorem guest_width_806 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput907 = true := by decide_cbv
theorem guest_width_807 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput908 = true := by decide_cbv
theorem guest_width_808 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput909 = true := by decide_cbv
theorem guest_width_809 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput910 = true := by decide_cbv
theorem guest_width_810 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput911 = true := by decide_cbv
theorem guest_width_811 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput912 = true := by decide_cbv
theorem guest_width_812 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput913 = true := by decide_cbv
theorem guest_width_813 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput914 = true := by decide_cbv
theorem guest_width_814 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput915 = true := by decide_cbv
theorem guest_width_815 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput916 = true := by decide_cbv
theorem guest_width_816 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput917 = true := by decide_cbv
theorem guest_width_817 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput918 = true := by decide_cbv
theorem guest_width_818 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput919 = true := by decide_cbv
theorem guest_width_819 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput920 = true := by decide_cbv
theorem guest_width_820 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput921 = true := by decide_cbv
theorem guest_width_821 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput922 = true := by decide_cbv
theorem guest_width_822 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput923 = true := by decide_cbv
theorem guest_width_823 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput924 = true := by decide_cbv
theorem guest_width_824 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput925 = true := by decide_cbv
theorem guest_width_825 : guestWidthDecl InitECandidate.Proofs.FrontendStages.Declarations.globalOutput926 = true := by decide_cbv

theorem guest_inputs_width : ∀ d ∈ InitECandidate.Proofs.FrontendStages.Crep.inputFunctions,
    guestWidthDecl d = true := by
  unfold InitECandidate.Proofs.FrontendStages.Crep.inputFunctions
  refine width_step guest_width_0 ?_
  refine width_step guest_width_1 ?_
  refine width_step guest_width_2 ?_
  refine width_step guest_width_3 ?_
  refine width_step guest_width_4 ?_
  refine width_step guest_width_5 ?_
  refine width_step guest_width_6 ?_
  refine width_step guest_width_7 ?_
  refine width_step guest_width_8 ?_
  refine width_step guest_width_9 ?_
  refine width_step guest_width_10 ?_
  refine width_step guest_width_11 ?_
  refine width_step guest_width_12 ?_
  refine width_step guest_width_13 ?_
  refine width_step guest_width_14 ?_
  refine width_step guest_width_15 ?_
  refine width_step guest_width_16 ?_
  refine width_step guest_width_17 ?_
  refine width_step guest_width_18 ?_
  refine width_step guest_width_19 ?_
  refine width_step guest_width_20 ?_
  refine width_step guest_width_21 ?_
  refine width_step guest_width_22 ?_
  refine width_step guest_width_23 ?_
  refine width_step guest_width_24 ?_
  refine width_step guest_width_25 ?_
  refine width_step guest_width_26 ?_
  refine width_step guest_width_27 ?_
  refine width_step guest_width_28 ?_
  refine width_step guest_width_29 ?_
  refine width_step guest_width_30 ?_
  refine width_step guest_width_31 ?_
  refine width_step guest_width_32 ?_
  refine width_step guest_width_33 ?_
  refine width_step guest_width_34 ?_
  refine width_step guest_width_35 ?_
  refine width_step guest_width_36 ?_
  refine width_step guest_width_37 ?_
  refine width_step guest_width_38 ?_
  refine width_step guest_width_39 ?_
  refine width_step guest_width_40 ?_
  refine width_step guest_width_41 ?_
  refine width_step guest_width_42 ?_
  refine width_step guest_width_43 ?_
  refine width_step guest_width_44 ?_
  refine width_step guest_width_45 ?_
  refine width_step guest_width_46 ?_
  refine width_step guest_width_47 ?_
  refine width_step guest_width_48 ?_
  refine width_step guest_width_49 ?_
  refine width_step guest_width_50 ?_
  refine width_step guest_width_51 ?_
  refine width_step guest_width_52 ?_
  refine width_step guest_width_53 ?_
  refine width_step guest_width_54 ?_
  refine width_step guest_width_55 ?_
  refine width_step guest_width_56 ?_
  refine width_step guest_width_57 ?_
  refine width_step guest_width_58 ?_
  refine width_step guest_width_59 ?_
  refine width_step guest_width_60 ?_
  refine width_step guest_width_61 ?_
  refine width_step guest_width_62 ?_
  refine width_step guest_width_63 ?_
  refine width_step guest_width_64 ?_
  refine width_step guest_width_65 ?_
  refine width_step guest_width_66 ?_
  refine width_step guest_width_67 ?_
  refine width_step guest_width_68 ?_
  refine width_step guest_width_69 ?_
  refine width_step guest_width_70 ?_
  refine width_step guest_width_71 ?_
  refine width_step guest_width_72 ?_
  refine width_step guest_width_73 ?_
  refine width_step guest_width_74 ?_
  refine width_step guest_width_75 ?_
  refine width_step guest_width_76 ?_
  refine width_step guest_width_77 ?_
  refine width_step guest_width_78 ?_
  refine width_step guest_width_79 ?_
  refine width_step guest_width_80 ?_
  refine width_step guest_width_81 ?_
  refine width_step guest_width_82 ?_
  refine width_step guest_width_83 ?_
  refine width_step guest_width_84 ?_
  refine width_step guest_width_85 ?_
  refine width_step guest_width_86 ?_
  refine width_step guest_width_87 ?_
  refine width_step guest_width_88 ?_
  refine width_step guest_width_89 ?_
  refine width_step guest_width_90 ?_
  refine width_step guest_width_91 ?_
  refine width_step guest_width_92 ?_
  refine width_step guest_width_93 ?_
  refine width_step guest_width_94 ?_
  refine width_step guest_width_95 ?_
  refine width_step guest_width_96 ?_
  refine width_step guest_width_97 ?_
  refine width_step guest_width_98 ?_
  refine width_step guest_width_99 ?_
  refine width_step guest_width_100 ?_
  refine width_step guest_width_101 ?_
  refine width_step guest_width_102 ?_
  refine width_step guest_width_103 ?_
  refine width_step guest_width_104 ?_
  refine width_step guest_width_105 ?_
  refine width_step guest_width_106 ?_
  refine width_step guest_width_107 ?_
  refine width_step guest_width_108 ?_
  refine width_step guest_width_109 ?_
  refine width_step guest_width_110 ?_
  refine width_step guest_width_111 ?_
  refine width_step guest_width_112 ?_
  refine width_step guest_width_113 ?_
  refine width_step guest_width_114 ?_
  refine width_step guest_width_115 ?_
  refine width_step guest_width_116 ?_
  refine width_step guest_width_117 ?_
  refine width_step guest_width_118 ?_
  refine width_step guest_width_119 ?_
  refine width_step guest_width_120 ?_
  refine width_step guest_width_121 ?_
  refine width_step guest_width_122 ?_
  refine width_step guest_width_123 ?_
  refine width_step guest_width_124 ?_
  refine width_step guest_width_125 ?_
  refine width_step guest_width_126 ?_
  refine width_step guest_width_127 ?_
  refine width_step guest_width_128 ?_
  refine width_step guest_width_129 ?_
  refine width_step guest_width_130 ?_
  refine width_step guest_width_131 ?_
  refine width_step guest_width_132 ?_
  refine width_step guest_width_133 ?_
  refine width_step guest_width_134 ?_
  refine width_step guest_width_135 ?_
  refine width_step guest_width_136 ?_
  refine width_step guest_width_137 ?_
  refine width_step guest_width_138 ?_
  refine width_step guest_width_139 ?_
  refine width_step guest_width_140 ?_
  refine width_step guest_width_141 ?_
  refine width_step guest_width_142 ?_
  refine width_step guest_width_143 ?_
  refine width_step guest_width_144 ?_
  refine width_step guest_width_145 ?_
  refine width_step guest_width_146 ?_
  refine width_step guest_width_147 ?_
  refine width_step guest_width_148 ?_
  refine width_step guest_width_149 ?_
  refine width_step guest_width_150 ?_
  refine width_step guest_width_151 ?_
  refine width_step guest_width_152 ?_
  refine width_step guest_width_153 ?_
  refine width_step guest_width_154 ?_
  refine width_step guest_width_155 ?_
  refine width_step guest_width_156 ?_
  refine width_step guest_width_157 ?_
  refine width_step guest_width_158 ?_
  refine width_step guest_width_159 ?_
  refine width_step guest_width_160 ?_
  refine width_step guest_width_161 ?_
  refine width_step guest_width_162 ?_
  refine width_step guest_width_163 ?_
  refine width_step guest_width_164 ?_
  refine width_step guest_width_165 ?_
  refine width_step guest_width_166 ?_
  refine width_step guest_width_167 ?_
  refine width_step guest_width_168 ?_
  refine width_step guest_width_169 ?_
  refine width_step guest_width_170 ?_
  refine width_step guest_width_171 ?_
  refine width_step guest_width_172 ?_
  refine width_step guest_width_173 ?_
  refine width_step guest_width_174 ?_
  refine width_step guest_width_175 ?_
  refine width_step guest_width_176 ?_
  refine width_step guest_width_177 ?_
  refine width_step guest_width_178 ?_
  refine width_step guest_width_179 ?_
  refine width_step guest_width_180 ?_
  refine width_step guest_width_181 ?_
  refine width_step guest_width_182 ?_
  refine width_step guest_width_183 ?_
  refine width_step guest_width_184 ?_
  refine width_step guest_width_185 ?_
  refine width_step guest_width_186 ?_
  refine width_step guest_width_187 ?_
  refine width_step guest_width_188 ?_
  refine width_step guest_width_189 ?_
  refine width_step guest_width_190 ?_
  refine width_step guest_width_191 ?_
  refine width_step guest_width_192 ?_
  refine width_step guest_width_193 ?_
  refine width_step guest_width_194 ?_
  refine width_step guest_width_195 ?_
  refine width_step guest_width_196 ?_
  refine width_step guest_width_197 ?_
  refine width_step guest_width_198 ?_
  refine width_step guest_width_199 ?_
  refine width_step guest_width_200 ?_
  refine width_step guest_width_201 ?_
  refine width_step guest_width_202 ?_
  refine width_step guest_width_203 ?_
  refine width_step guest_width_204 ?_
  refine width_step guest_width_205 ?_
  refine width_step guest_width_206 ?_
  refine width_step guest_width_207 ?_
  refine width_step guest_width_208 ?_
  refine width_step guest_width_209 ?_
  refine width_step guest_width_210 ?_
  refine width_step guest_width_211 ?_
  refine width_step guest_width_212 ?_
  refine width_step guest_width_213 ?_
  refine width_step guest_width_214 ?_
  refine width_step guest_width_215 ?_
  refine width_step guest_width_216 ?_
  refine width_step guest_width_217 ?_
  refine width_step guest_width_218 ?_
  refine width_step guest_width_219 ?_
  refine width_step guest_width_220 ?_
  refine width_step guest_width_221 ?_
  refine width_step guest_width_222 ?_
  refine width_step guest_width_223 ?_
  refine width_step guest_width_224 ?_
  refine width_step guest_width_225 ?_
  refine width_step guest_width_226 ?_
  refine width_step guest_width_227 ?_
  refine width_step guest_width_228 ?_
  refine width_step guest_width_229 ?_
  refine width_step guest_width_230 ?_
  refine width_step guest_width_231 ?_
  refine width_step guest_width_232 ?_
  refine width_step guest_width_233 ?_
  refine width_step guest_width_234 ?_
  refine width_step guest_width_235 ?_
  refine width_step guest_width_236 ?_
  refine width_step guest_width_237 ?_
  refine width_step guest_width_238 ?_
  refine width_step guest_width_239 ?_
  refine width_step guest_width_240 ?_
  refine width_step guest_width_241 ?_
  refine width_step guest_width_242 ?_
  refine width_step guest_width_243 ?_
  refine width_step guest_width_244 ?_
  refine width_step guest_width_245 ?_
  refine width_step guest_width_246 ?_
  refine width_step guest_width_247 ?_
  refine width_step guest_width_248 ?_
  refine width_step guest_width_249 ?_
  refine width_step guest_width_250 ?_
  refine width_step guest_width_251 ?_
  refine width_step guest_width_252 ?_
  refine width_step guest_width_253 ?_
  refine width_step guest_width_254 ?_
  refine width_step guest_width_255 ?_
  refine width_step guest_width_256 ?_
  refine width_step guest_width_257 ?_
  refine width_step guest_width_258 ?_
  refine width_step guest_width_259 ?_
  refine width_step guest_width_260 ?_
  refine width_step guest_width_261 ?_
  refine width_step guest_width_262 ?_
  refine width_step guest_width_263 ?_
  refine width_step guest_width_264 ?_
  refine width_step guest_width_265 ?_
  refine width_step guest_width_266 ?_
  refine width_step guest_width_267 ?_
  refine width_step guest_width_268 ?_
  refine width_step guest_width_269 ?_
  refine width_step guest_width_270 ?_
  refine width_step guest_width_271 ?_
  refine width_step guest_width_272 ?_
  refine width_step guest_width_273 ?_
  refine width_step guest_width_274 ?_
  refine width_step guest_width_275 ?_
  refine width_step guest_width_276 ?_
  refine width_step guest_width_277 ?_
  refine width_step guest_width_278 ?_
  refine width_step guest_width_279 ?_
  refine width_step guest_width_280 ?_
  refine width_step guest_width_281 ?_
  refine width_step guest_width_282 ?_
  refine width_step guest_width_283 ?_
  refine width_step guest_width_284 ?_
  refine width_step guest_width_285 ?_
  refine width_step guest_width_286 ?_
  refine width_step guest_width_287 ?_
  refine width_step guest_width_288 ?_
  refine width_step guest_width_289 ?_
  refine width_step guest_width_290 ?_
  refine width_step guest_width_291 ?_
  refine width_step guest_width_292 ?_
  refine width_step guest_width_293 ?_
  refine width_step guest_width_294 ?_
  refine width_step guest_width_295 ?_
  refine width_step guest_width_296 ?_
  refine width_step guest_width_297 ?_
  refine width_step guest_width_298 ?_
  refine width_step guest_width_299 ?_
  refine width_step guest_width_300 ?_
  refine width_step guest_width_301 ?_
  refine width_step guest_width_302 ?_
  refine width_step guest_width_303 ?_
  refine width_step guest_width_304 ?_
  refine width_step guest_width_305 ?_
  refine width_step guest_width_306 ?_
  refine width_step guest_width_307 ?_
  refine width_step guest_width_308 ?_
  refine width_step guest_width_309 ?_
  refine width_step guest_width_310 ?_
  refine width_step guest_width_311 ?_
  refine width_step guest_width_312 ?_
  refine width_step guest_width_313 ?_
  refine width_step guest_width_314 ?_
  refine width_step guest_width_315 ?_
  refine width_step guest_width_316 ?_
  refine width_step guest_width_317 ?_
  refine width_step guest_width_318 ?_
  refine width_step guest_width_319 ?_
  refine width_step guest_width_320 ?_
  refine width_step guest_width_321 ?_
  refine width_step guest_width_322 ?_
  refine width_step guest_width_323 ?_
  refine width_step guest_width_324 ?_
  refine width_step guest_width_325 ?_
  refine width_step guest_width_326 ?_
  refine width_step guest_width_327 ?_
  refine width_step guest_width_328 ?_
  refine width_step guest_width_329 ?_
  refine width_step guest_width_330 ?_
  refine width_step guest_width_331 ?_
  refine width_step guest_width_332 ?_
  refine width_step guest_width_333 ?_
  refine width_step guest_width_334 ?_
  refine width_step guest_width_335 ?_
  refine width_step guest_width_336 ?_
  refine width_step guest_width_337 ?_
  refine width_step guest_width_338 ?_
  refine width_step guest_width_339 ?_
  refine width_step guest_width_340 ?_
  refine width_step guest_width_341 ?_
  refine width_step guest_width_342 ?_
  refine width_step guest_width_343 ?_
  refine width_step guest_width_344 ?_
  refine width_step guest_width_345 ?_
  refine width_step guest_width_346 ?_
  refine width_step guest_width_347 ?_
  refine width_step guest_width_348 ?_
  refine width_step guest_width_349 ?_
  refine width_step guest_width_350 ?_
  refine width_step guest_width_351 ?_
  refine width_step guest_width_352 ?_
  refine width_step guest_width_353 ?_
  refine width_step guest_width_354 ?_
  refine width_step guest_width_355 ?_
  refine width_step guest_width_356 ?_
  refine width_step guest_width_357 ?_
  refine width_step guest_width_358 ?_
  refine width_step guest_width_359 ?_
  refine width_step guest_width_360 ?_
  refine width_step guest_width_361 ?_
  refine width_step guest_width_362 ?_
  refine width_step guest_width_363 ?_
  refine width_step guest_width_364 ?_
  refine width_step guest_width_365 ?_
  refine width_step guest_width_366 ?_
  refine width_step guest_width_367 ?_
  refine width_step guest_width_368 ?_
  refine width_step guest_width_369 ?_
  refine width_step guest_width_370 ?_
  refine width_step guest_width_371 ?_
  refine width_step guest_width_372 ?_
  refine width_step guest_width_373 ?_
  refine width_step guest_width_374 ?_
  refine width_step guest_width_375 ?_
  refine width_step guest_width_376 ?_
  refine width_step guest_width_377 ?_
  refine width_step guest_width_378 ?_
  refine width_step guest_width_379 ?_
  refine width_step guest_width_380 ?_
  refine width_step guest_width_381 ?_
  refine width_step guest_width_382 ?_
  refine width_step guest_width_383 ?_
  refine width_step guest_width_384 ?_
  refine width_step guest_width_385 ?_
  refine width_step guest_width_386 ?_
  refine width_step guest_width_387 ?_
  refine width_step guest_width_388 ?_
  refine width_step guest_width_389 ?_
  refine width_step guest_width_390 ?_
  refine width_step guest_width_391 ?_
  refine width_step guest_width_392 ?_
  refine width_step guest_width_393 ?_
  refine width_step guest_width_394 ?_
  refine width_step guest_width_395 ?_
  refine width_step guest_width_396 ?_
  refine width_step guest_width_397 ?_
  refine width_step guest_width_398 ?_
  refine width_step guest_width_399 ?_
  refine width_step guest_width_400 ?_
  refine width_step guest_width_401 ?_
  refine width_step guest_width_402 ?_
  refine width_step guest_width_403 ?_
  refine width_step guest_width_404 ?_
  refine width_step guest_width_405 ?_
  refine width_step guest_width_406 ?_
  refine width_step guest_width_407 ?_
  refine width_step guest_width_408 ?_
  refine width_step guest_width_409 ?_
  refine width_step guest_width_410 ?_
  refine width_step guest_width_411 ?_
  refine width_step guest_width_412 ?_
  refine width_step guest_width_413 ?_
  refine width_step guest_width_414 ?_
  refine width_step guest_width_415 ?_
  refine width_step guest_width_416 ?_
  refine width_step guest_width_417 ?_
  refine width_step guest_width_418 ?_
  refine width_step guest_width_419 ?_
  refine width_step guest_width_420 ?_
  refine width_step guest_width_421 ?_
  refine width_step guest_width_422 ?_
  refine width_step guest_width_423 ?_
  refine width_step guest_width_424 ?_
  refine width_step guest_width_425 ?_
  refine width_step guest_width_426 ?_
  refine width_step guest_width_427 ?_
  refine width_step guest_width_428 ?_
  refine width_step guest_width_429 ?_
  refine width_step guest_width_430 ?_
  refine width_step guest_width_431 ?_
  refine width_step guest_width_432 ?_
  refine width_step guest_width_433 ?_
  refine width_step guest_width_434 ?_
  refine width_step guest_width_435 ?_
  refine width_step guest_width_436 ?_
  refine width_step guest_width_437 ?_
  refine width_step guest_width_438 ?_
  refine width_step guest_width_439 ?_
  refine width_step guest_width_440 ?_
  refine width_step guest_width_441 ?_
  refine width_step guest_width_442 ?_
  refine width_step guest_width_443 ?_
  refine width_step guest_width_444 ?_
  refine width_step guest_width_445 ?_
  refine width_step guest_width_446 ?_
  refine width_step guest_width_447 ?_
  refine width_step guest_width_448 ?_
  refine width_step guest_width_449 ?_
  refine width_step guest_width_450 ?_
  refine width_step guest_width_451 ?_
  refine width_step guest_width_452 ?_
  refine width_step guest_width_453 ?_
  refine width_step guest_width_454 ?_
  refine width_step guest_width_455 ?_
  refine width_step guest_width_456 ?_
  refine width_step guest_width_457 ?_
  refine width_step guest_width_458 ?_
  refine width_step guest_width_459 ?_
  refine width_step guest_width_460 ?_
  refine width_step guest_width_461 ?_
  refine width_step guest_width_462 ?_
  refine width_step guest_width_463 ?_
  refine width_step guest_width_464 ?_
  refine width_step guest_width_465 ?_
  refine width_step guest_width_466 ?_
  refine width_step guest_width_467 ?_
  refine width_step guest_width_468 ?_
  refine width_step guest_width_469 ?_
  refine width_step guest_width_470 ?_
  refine width_step guest_width_471 ?_
  refine width_step guest_width_472 ?_
  refine width_step guest_width_473 ?_
  refine width_step guest_width_474 ?_
  refine width_step guest_width_475 ?_
  refine width_step guest_width_476 ?_
  refine width_step guest_width_477 ?_
  refine width_step guest_width_478 ?_
  refine width_step guest_width_479 ?_
  refine width_step guest_width_480 ?_
  refine width_step guest_width_481 ?_
  refine width_step guest_width_482 ?_
  refine width_step guest_width_483 ?_
  refine width_step guest_width_484 ?_
  refine width_step guest_width_485 ?_
  refine width_step guest_width_486 ?_
  refine width_step guest_width_487 ?_
  refine width_step guest_width_488 ?_
  refine width_step guest_width_489 ?_
  refine width_step guest_width_490 ?_
  refine width_step guest_width_491 ?_
  refine width_step guest_width_492 ?_
  refine width_step guest_width_493 ?_
  refine width_step guest_width_494 ?_
  refine width_step guest_width_495 ?_
  refine width_step guest_width_496 ?_
  refine width_step guest_width_497 ?_
  refine width_step guest_width_498 ?_
  refine width_step guest_width_499 ?_
  refine width_step guest_width_500 ?_
  refine width_step guest_width_501 ?_
  refine width_step guest_width_502 ?_
  refine width_step guest_width_503 ?_
  refine width_step guest_width_504 ?_
  refine width_step guest_width_505 ?_
  refine width_step guest_width_506 ?_
  refine width_step guest_width_507 ?_
  refine width_step guest_width_508 ?_
  refine width_step guest_width_509 ?_
  refine width_step guest_width_510 ?_
  refine width_step guest_width_511 ?_
  refine width_step guest_width_512 ?_
  refine width_step guest_width_513 ?_
  refine width_step guest_width_514 ?_
  refine width_step guest_width_515 ?_
  refine width_step guest_width_516 ?_
  refine width_step guest_width_517 ?_
  refine width_step guest_width_518 ?_
  refine width_step guest_width_519 ?_
  refine width_step guest_width_520 ?_
  refine width_step guest_width_521 ?_
  refine width_step guest_width_522 ?_
  refine width_step guest_width_523 ?_
  refine width_step guest_width_524 ?_
  refine width_step guest_width_525 ?_
  refine width_step guest_width_526 ?_
  refine width_step guest_width_527 ?_
  refine width_step guest_width_528 ?_
  refine width_step guest_width_529 ?_
  refine width_step guest_width_530 ?_
  refine width_step guest_width_531 ?_
  refine width_step guest_width_532 ?_
  refine width_step guest_width_533 ?_
  refine width_step guest_width_534 ?_
  refine width_step guest_width_535 ?_
  refine width_step guest_width_536 ?_
  refine width_step guest_width_537 ?_
  refine width_step guest_width_538 ?_
  refine width_step guest_width_539 ?_
  refine width_step guest_width_540 ?_
  refine width_step guest_width_541 ?_
  refine width_step guest_width_542 ?_
  refine width_step guest_width_543 ?_
  refine width_step guest_width_544 ?_
  refine width_step guest_width_545 ?_
  refine width_step guest_width_546 ?_
  refine width_step guest_width_547 ?_
  refine width_step guest_width_548 ?_
  refine width_step guest_width_549 ?_
  refine width_step guest_width_550 ?_
  refine width_step guest_width_551 ?_
  refine width_step guest_width_552 ?_
  refine width_step guest_width_553 ?_
  refine width_step guest_width_554 ?_
  refine width_step guest_width_555 ?_
  refine width_step guest_width_556 ?_
  refine width_step guest_width_557 ?_
  refine width_step guest_width_558 ?_
  refine width_step guest_width_559 ?_
  refine width_step guest_width_560 ?_
  refine width_step guest_width_561 ?_
  refine width_step guest_width_562 ?_
  refine width_step guest_width_563 ?_
  refine width_step guest_width_564 ?_
  refine width_step guest_width_565 ?_
  refine width_step guest_width_566 ?_
  refine width_step guest_width_567 ?_
  refine width_step guest_width_568 ?_
  refine width_step guest_width_569 ?_
  refine width_step guest_width_570 ?_
  refine width_step guest_width_571 ?_
  refine width_step guest_width_572 ?_
  refine width_step guest_width_573 ?_
  refine width_step guest_width_574 ?_
  refine width_step guest_width_575 ?_
  refine width_step guest_width_576 ?_
  refine width_step guest_width_577 ?_
  refine width_step guest_width_578 ?_
  refine width_step guest_width_579 ?_
  refine width_step guest_width_580 ?_
  refine width_step guest_width_581 ?_
  refine width_step guest_width_582 ?_
  refine width_step guest_width_583 ?_
  refine width_step guest_width_584 ?_
  refine width_step guest_width_585 ?_
  refine width_step guest_width_586 ?_
  refine width_step guest_width_587 ?_
  refine width_step guest_width_588 ?_
  refine width_step guest_width_589 ?_
  refine width_step guest_width_590 ?_
  refine width_step guest_width_591 ?_
  refine width_step guest_width_592 ?_
  refine width_step guest_width_593 ?_
  refine width_step guest_width_594 ?_
  refine width_step guest_width_595 ?_
  refine width_step guest_width_596 ?_
  refine width_step guest_width_597 ?_
  refine width_step guest_width_598 ?_
  refine width_step guest_width_599 ?_
  refine width_step guest_width_600 ?_
  refine width_step guest_width_601 ?_
  refine width_step guest_width_602 ?_
  refine width_step guest_width_603 ?_
  refine width_step guest_width_604 ?_
  refine width_step guest_width_605 ?_
  refine width_step guest_width_606 ?_
  refine width_step guest_width_607 ?_
  refine width_step guest_width_608 ?_
  refine width_step guest_width_609 ?_
  refine width_step guest_width_610 ?_
  refine width_step guest_width_611 ?_
  refine width_step guest_width_612 ?_
  refine width_step guest_width_613 ?_
  refine width_step guest_width_614 ?_
  refine width_step guest_width_615 ?_
  refine width_step guest_width_616 ?_
  refine width_step guest_width_617 ?_
  refine width_step guest_width_618 ?_
  refine width_step guest_width_619 ?_
  refine width_step guest_width_620 ?_
  refine width_step guest_width_621 ?_
  refine width_step guest_width_622 ?_
  refine width_step guest_width_623 ?_
  refine width_step guest_width_624 ?_
  refine width_step guest_width_625 ?_
  refine width_step guest_width_626 ?_
  refine width_step guest_width_627 ?_
  refine width_step guest_width_628 ?_
  refine width_step guest_width_629 ?_
  refine width_step guest_width_630 ?_
  refine width_step guest_width_631 ?_
  refine width_step guest_width_632 ?_
  refine width_step guest_width_633 ?_
  refine width_step guest_width_634 ?_
  refine width_step guest_width_635 ?_
  refine width_step guest_width_636 ?_
  refine width_step guest_width_637 ?_
  refine width_step guest_width_638 ?_
  refine width_step guest_width_639 ?_
  refine width_step guest_width_640 ?_
  refine width_step guest_width_641 ?_
  refine width_step guest_width_642 ?_
  refine width_step guest_width_643 ?_
  refine width_step guest_width_644 ?_
  refine width_step guest_width_645 ?_
  refine width_step guest_width_646 ?_
  refine width_step guest_width_647 ?_
  refine width_step guest_width_648 ?_
  refine width_step guest_width_649 ?_
  refine width_step guest_width_650 ?_
  refine width_step guest_width_651 ?_
  refine width_step guest_width_652 ?_
  refine width_step guest_width_653 ?_
  refine width_step guest_width_654 ?_
  refine width_step guest_width_655 ?_
  refine width_step guest_width_656 ?_
  refine width_step guest_width_657 ?_
  refine width_step guest_width_658 ?_
  refine width_step guest_width_659 ?_
  refine width_step guest_width_660 ?_
  refine width_step guest_width_661 ?_
  refine width_step guest_width_662 ?_
  refine width_step guest_width_663 ?_
  refine width_step guest_width_664 ?_
  refine width_step guest_width_665 ?_
  refine width_step guest_width_666 ?_
  refine width_step guest_width_667 ?_
  refine width_step guest_width_668 ?_
  refine width_step guest_width_669 ?_
  refine width_step guest_width_670 ?_
  refine width_step guest_width_671 ?_
  refine width_step guest_width_672 ?_
  refine width_step guest_width_673 ?_
  refine width_step guest_width_674 ?_
  refine width_step guest_width_675 ?_
  refine width_step guest_width_676 ?_
  refine width_step guest_width_677 ?_
  refine width_step guest_width_678 ?_
  refine width_step guest_width_679 ?_
  refine width_step guest_width_680 ?_
  refine width_step guest_width_681 ?_
  refine width_step guest_width_682 ?_
  refine width_step guest_width_683 ?_
  refine width_step guest_width_684 ?_
  refine width_step guest_width_685 ?_
  refine width_step guest_width_686 ?_
  refine width_step guest_width_687 ?_
  refine width_step guest_width_688 ?_
  refine width_step guest_width_689 ?_
  refine width_step guest_width_690 ?_
  refine width_step guest_width_691 ?_
  refine width_step guest_width_692 ?_
  refine width_step guest_width_693 ?_
  refine width_step guest_width_694 ?_
  refine width_step guest_width_695 ?_
  refine width_step guest_width_696 ?_
  refine width_step guest_width_697 ?_
  refine width_step guest_width_698 ?_
  refine width_step guest_width_699 ?_
  refine width_step guest_width_700 ?_
  refine width_step guest_width_701 ?_
  refine width_step guest_width_702 ?_
  refine width_step guest_width_703 ?_
  refine width_step guest_width_704 ?_
  refine width_step guest_width_705 ?_
  refine width_step guest_width_706 ?_
  refine width_step guest_width_707 ?_
  refine width_step guest_width_708 ?_
  refine width_step guest_width_709 ?_
  refine width_step guest_width_710 ?_
  refine width_step guest_width_711 ?_
  refine width_step guest_width_712 ?_
  refine width_step guest_width_713 ?_
  refine width_step guest_width_714 ?_
  refine width_step guest_width_715 ?_
  refine width_step guest_width_716 ?_
  refine width_step guest_width_717 ?_
  refine width_step guest_width_718 ?_
  refine width_step guest_width_719 ?_
  refine width_step guest_width_720 ?_
  refine width_step guest_width_721 ?_
  refine width_step guest_width_722 ?_
  refine width_step guest_width_723 ?_
  refine width_step guest_width_724 ?_
  refine width_step guest_width_725 ?_
  refine width_step guest_width_726 ?_
  refine width_step guest_width_727 ?_
  refine width_step guest_width_728 ?_
  refine width_step guest_width_729 ?_
  refine width_step guest_width_730 ?_
  refine width_step guest_width_731 ?_
  refine width_step guest_width_732 ?_
  refine width_step guest_width_733 ?_
  refine width_step guest_width_734 ?_
  refine width_step guest_width_735 ?_
  refine width_step guest_width_736 ?_
  refine width_step guest_width_737 ?_
  refine width_step guest_width_738 ?_
  refine width_step guest_width_739 ?_
  refine width_step guest_width_740 ?_
  refine width_step guest_width_741 ?_
  refine width_step guest_width_742 ?_
  refine width_step guest_width_743 ?_
  refine width_step guest_width_744 ?_
  refine width_step guest_width_745 ?_
  refine width_step guest_width_746 ?_
  refine width_step guest_width_747 ?_
  refine width_step guest_width_748 ?_
  refine width_step guest_width_749 ?_
  refine width_step guest_width_750 ?_
  refine width_step guest_width_751 ?_
  refine width_step guest_width_752 ?_
  refine width_step guest_width_753 ?_
  refine width_step guest_width_754 ?_
  refine width_step guest_width_755 ?_
  refine width_step guest_width_756 ?_
  refine width_step guest_width_757 ?_
  refine width_step guest_width_758 ?_
  refine width_step guest_width_759 ?_
  refine width_step guest_width_760 ?_
  refine width_step guest_width_761 ?_
  refine width_step guest_width_762 ?_
  refine width_step guest_width_763 ?_
  refine width_step guest_width_764 ?_
  refine width_step guest_width_765 ?_
  refine width_step guest_width_766 ?_
  refine width_step guest_width_767 ?_
  refine width_step guest_width_768 ?_
  refine width_step guest_width_769 ?_
  refine width_step guest_width_770 ?_
  refine width_step guest_width_771 ?_
  refine width_step guest_width_772 ?_
  refine width_step guest_width_773 ?_
  refine width_step guest_width_774 ?_
  refine width_step guest_width_775 ?_
  refine width_step guest_width_776 ?_
  refine width_step guest_width_777 ?_
  refine width_step guest_width_778 ?_
  refine width_step guest_width_779 ?_
  refine width_step guest_width_780 ?_
  refine width_step guest_width_781 ?_
  refine width_step guest_width_782 ?_
  refine width_step guest_width_783 ?_
  refine width_step guest_width_784 ?_
  refine width_step guest_width_785 ?_
  refine width_step guest_width_786 ?_
  refine width_step guest_width_787 ?_
  refine width_step guest_width_788 ?_
  refine width_step guest_width_789 ?_
  refine width_step guest_width_790 ?_
  refine width_step guest_width_791 ?_
  refine width_step guest_width_792 ?_
  refine width_step guest_width_793 ?_
  refine width_step guest_width_794 ?_
  refine width_step guest_width_795 ?_
  refine width_step guest_width_796 ?_
  refine width_step guest_width_797 ?_
  refine width_step guest_width_798 ?_
  refine width_step guest_width_799 ?_
  refine width_step guest_width_800 ?_
  refine width_step guest_width_801 ?_
  refine width_step guest_width_802 ?_
  refine width_step guest_width_803 ?_
  refine width_step guest_width_804 ?_
  refine width_step guest_width_805 ?_
  refine width_step guest_width_806 ?_
  refine width_step guest_width_807 ?_
  refine width_step guest_width_808 ?_
  refine width_step guest_width_809 ?_
  refine width_step guest_width_810 ?_
  refine width_step guest_width_811 ?_
  refine width_step guest_width_812 ?_
  refine width_step guest_width_813 ?_
  refine width_step guest_width_814 ?_
  refine width_step guest_width_815 ?_
  refine width_step guest_width_816 ?_
  refine width_step guest_width_817 ?_
  refine width_step guest_width_818 ?_
  refine width_step guest_width_819 ?_
  refine width_step guest_width_820 ?_
  refine width_step guest_width_821 ?_
  refine width_step guest_width_822 ?_
  refine width_step guest_width_823 ?_
  refine width_step guest_width_824 ?_
  refine width_step guest_width_825 ?_
  intro x hx; cases hx

#print axioms guest_inputs_width
end InitECandidate.Runtime.FineCost
