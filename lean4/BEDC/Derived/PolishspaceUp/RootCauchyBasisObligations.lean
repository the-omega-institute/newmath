import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceRootCauchyBasisObligations [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance localName
      basisRead completionRead denseRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric ->
      UnaryHistory complete ->
        UnaryHistory separable ->
          UnaryHistory stream ->
            UnaryHistory readback ->
              UnaryHistory ledger ->
                UnaryHistory alignment ->
                  UnaryHistory transport ->
                    Cont metric complete completionRead ->
                      Cont metric separable denseRead ->
                        Cont completionRead denseRead basisRead ->
                          Cont ledger transport route ->
                            Cont route readback rootRead ->
                              PkgSig bundle provenance pkg ->
                                PkgSig bundle localName pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row rootRead /\ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row metric \/ hsame row complete \/
                                          hsame row separable \/ hsame row alignment \/
                                            hsame row rootRead)
                                      (fun row : BHist =>
                                        UnaryHistory row /\ PkgSig bundle provenance pkg /\
                                          PkgSig bundle localName pkg)
                                      hsame /\
                                    UnaryHistory completionRead /\ UnaryHistory denseRead /\
                                      UnaryHistory basisRead /\ UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro metricUnary completeUnary separableUnary _streamUnary readbackUnary ledgerUnary
    _alignmentUnary transportUnary metricCompleteRead metricSeparableDense
    completionDenseBasis ledgerTransportRoute routeReadbackRoot provenancePkg localNamePkg
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricCompleteRead
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed metricUnary separableUnary metricSeparableDense
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed completionUnary denseUnary completionDenseBasis
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary readbackUnary routeReadbackRoot
  have sourceRoot :
      (fun row : BHist => hsame row rootRead /\ UnaryHistory row) rootRead := by
    exact And.intro (hsame_refl rootRead) rootUnary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric \/ hsame row complete \/ hsame row separable \/
              hsame row alignment \/ hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row /\ PkgSig bundle provenance pkg /\ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead sourceRoot
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
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact And.intro source.right (And.intro provenancePkg localNamePkg)
  }
  exact
    And.intro cert
      (And.intro completionUnary (And.intro denseUnary (And.intro basisUnary rootUnary)))

end BEDC.Derived.PolishspaceUp
