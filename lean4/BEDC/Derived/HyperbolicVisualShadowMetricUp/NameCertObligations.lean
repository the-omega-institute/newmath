import BEDC.Derived.HyperbolicVisualShadowMetricUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HyperbolicVisualShadowMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperbolicVisualShadowMetricNamecertObligations [AskSetup] [PackageSetup]
    {disk shadow metric visual busemann phase metricRead visualRead boundaryRead finalRead
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory disk →
      UnaryHistory shadow →
        UnaryHistory metric →
          UnaryHistory visual →
            UnaryHistory busemann →
              UnaryHistory phase →
                Cont disk shadow metricRead →
                  Cont metric visual visualRead →
                    Cont visualRead busemann boundaryRead →
                      Cont boundaryRead phase finalRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row disk ∨ hsame row shadow ∨ hsame row metric ∨
                                    hsame row visual ∨ hsame row busemann ∨
                                      hsame row phase ∨ hsame row finalRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont disk shadow metricRead ∧
                                    Cont metric visual visualRead ∧
                                      Cont visualRead busemann boundaryRead ∧
                                        Cont boundaryRead phase finalRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory metricRead ∧ UnaryHistory visualRead ∧
                                UnaryHistory boundaryRead ∧ UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro diskUnary shadowUnary metricUnary visualUnary busemannUnary phaseUnary metricRoute
    visualRoute boundaryRoute finalRoute provenancePkg localNamePkg
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed diskUnary shadowUnary metricRoute
  have visualReadUnary : UnaryHistory visualRead :=
    unary_cont_closed metricUnary visualUnary visualRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed visualReadUnary busemannUnary boundaryRoute
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed boundaryReadUnary phaseUnary finalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row disk ∨ hsame row shadow ∨ hsame row metric ∨
              hsame row visual ∨ hsame row busemann ∨ hsame row phase ∨
                hsame row finalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont disk shadow metricRead ∧ Cont metric visual visualRead ∧
              Cont visualRead busemann boundaryRead ∧ Cont boundaryRead phase finalRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finalRead ⟨hsame_refl finalRead, finalReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, metricRoute, visualRoute, boundaryRoute, finalRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, metricReadUnary, visualReadUnary, boundaryReadUnary, finalReadUnary⟩

end BEDC.Derived.HyperbolicVisualShadowMetricUp
