import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_strip_depth_readback_totality
    {Z S M R Q H C P N stripRead depthRead readback : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont M R depthRead ->
          Cont stripRead depthRead readback ->
            SemanticNameCert
                (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row readback ∧ Cont Z S stripRead ∧ Cont M R depthRead)
                (fun row : BHist =>
                  hsame row readback ∧ Cont stripRead depthRead readback)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory stripRead ∧ UnaryHistory depthRead ∧ UnaryHistory readback ∧
                  hsame H (append Z S) ∧ Cont Z S stripRead ∧ Cont M R depthRead ∧
                    Cont stripRead depthRead readback ∧ Cont M R Q ∧ Cont Q H C ∧
                      Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute depthRoute readbackRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed stripUnary depthUnary readbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readback ∧ Cont Z S stripRead ∧ Cont M R depthRead)
          (fun row : BHist => hsame row readback ∧ Cont stripRead depthRead readback)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback ⟨hsame_refl readback, readbackUnary⟩
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
      exact ⟨source.left, stripRoute, depthRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, readbackRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, stripUnary, depthUnary, readbackUnary,
      sameH, stripRoute, depthRoute, readbackRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
