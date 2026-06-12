import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_stdbridge_premise_surface
    {Z S M R Q H C P N image readback bridgePremise : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q image ->
        Cont image H readback ->
          Cont readback N bridgePremise ->
            SemanticNameCert
                (fun row : BHist => hsame row bridgePremise ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row image ∨
                    hsame row readback ∨ hsame row bridgePremise)
                (fun row : BHist =>
                  hsame row bridgePremise ∧ Cont readback N bridgePremise)
                hsame ∧ UnaryHistory image ∧ UnaryHistory readback ∧
              UnaryHistory bridgePremise ∧ hsame H (append Z S) ∧
                Cont (append Z S) Q image ∧ Cont image H readback ∧
                  Cont readback N bridgePremise := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet imageRoute readbackRoute bridgeRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have imageUnary : UnaryHistory image :=
    unary_cont_closed sourceUnary unaryQ imageRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed imageUnary unaryH readbackRoute
  have bridgeUnary : UnaryHistory bridgePremise :=
    unary_cont_closed readbackUnary unaryN bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgePremise ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row image ∨
              hsame row readback ∨ hsame row bridgePremise)
          (fun row : BHist => hsame row bridgePremise ∧ Cont readback N bridgePremise)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgePremise ⟨hsame_refl bridgePremise, bridgeUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, bridgeRoute⟩
  }
  exact
    ⟨cert, imageUnary, readbackUnary, bridgeUnary, sameH, imageRoute, readbackRoute,
      bridgeRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
