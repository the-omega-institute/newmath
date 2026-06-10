import BEDC.Derived.RealMetricUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealMetricLocatedDistanceHandoff [AskSetup] [PackageSetup]
    {X Y A D S R H C P N windowRead readbackRead toleranceRead absRead metricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealMetricCarrier X Y A D S R H C P N bundle pkg ->
      Cont S R windowRead ->
        Cont windowRead D toleranceRead ->
          Cont toleranceRead A absRead ->
            Cont absRead N metricRead ->
              PkgSig bundle metricRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row metricRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row Y ∨ hsame row S ∨ hsame row R ∨
                        hsame row D ∨ hsame row A ∨ hsame row metricRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S R windowRead ∧
                        Cont windowRead D toleranceRead ∧ Cont toleranceRead A absRead ∧
                          Cont absRead N metricRead ∧ PkgSig bundle metricRead pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧
                    UnaryHistory toleranceRead ∧ UnaryHistory absRead ∧
                      UnaryHistory metricRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute toleranceRoute absRoute metricRoute metricPkg
  have sUnary : UnaryHistory S := carrier.right.right.right.right.left
  have rUnary : UnaryHistory R := carrier.right.right.right.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.left
  have aUnary : UnaryHistory A := carrier.right.right.left
  have nUnary : UnaryHistory N :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary rUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary dUnary toleranceRoute
  have absUnary : UnaryHistory absRead :=
    unary_cont_closed toleranceUnary aUnary absRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed absUnary nUnary metricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row metricRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row A ∨ hsame row metricRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R windowRead ∧ Cont windowRead D toleranceRead ∧
              Cont toleranceRead A absRead ∧ Cont absRead N metricRead ∧
                PkgSig bundle metricRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro metricRead ⟨hsame_refl metricRead, metricUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, toleranceRoute, absRoute, metricRoute, metricPkg⟩
  }
  exact ⟨cert, windowUnary, toleranceUnary, absUnary, metricUnary⟩

end BEDC.Derived.RealMetricUp
