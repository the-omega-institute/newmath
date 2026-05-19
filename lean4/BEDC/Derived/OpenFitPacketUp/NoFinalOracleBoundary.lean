import BEDC.Derived.OpenFitPacketUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.OpenFitPacketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def OpenFitPacketCarrier (H Pi S M F E L B N : BHist) : Prop :=
  UnaryHistory H ∧ UnaryHistory Pi ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory F ∧
    UnaryHistory E ∧ UnaryHistory L ∧ UnaryHistory B ∧ UnaryHistory N ∧ Cont H Pi S ∧
      Cont S M F ∧ Cont F E L ∧ Cont L B N

theorem OpenFitPacket_no_final_oracle_boundary
    {H Pi S M F E L B N publicRead : BHist} :
    OpenFitPacketCarrier H Pi S M F E L B N ->
      Cont L B publicRead ->
        SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row publicRead ∧ Cont L B publicRead)
            (fun row : BHist =>
              hsame row publicRead ∧ Cont F E L ∧ Cont L B publicRead)
            hsame ∧
          UnaryHistory H ∧ UnaryHistory Pi ∧ UnaryHistory S ∧ UnaryHistory M ∧
            UnaryHistory F ∧ UnaryHistory E ∧ UnaryHistory L ∧ UnaryHistory B ∧
              UnaryHistory N ∧ UnaryHistory publicRead ∧ Cont H Pi S ∧ Cont S M F ∧
                Cont F E L ∧ Cont L B publicRead ∧ hsame publicRead N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier publicRoute
  obtain ⟨unaryH, unaryPi, unaryS, unaryM, unaryF, unaryE, unaryL, unaryB, unaryN,
    routeS, routeF, routeL, routeN⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed unaryL unaryB publicRoute
  have samePublicN : hsame publicRead N :=
    cont_deterministic publicRoute routeN
  have sourceAtPublic : hsame publicRead publicRead ∧ UnaryHistory publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row publicRead ∧ Cont L B publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont F E L ∧ Cont L B publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, publicRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routeL, publicRoute⟩
  }
  exact
    ⟨cert, unaryH, unaryPi, unaryS, unaryM, unaryF, unaryE, unaryL, unaryB, unaryN,
      publicUnary, routeS, routeF, routeL, publicRoute, samePublicN⟩

end BEDC.Derived.OpenFitPacketUp
