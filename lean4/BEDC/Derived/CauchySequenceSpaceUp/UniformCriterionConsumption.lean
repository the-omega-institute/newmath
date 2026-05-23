import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_uniformcriterion_consumption [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name handoff sealRow
      uniform : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont route name handoff ->
        Cont handoff completion sealRow ->
          Cont sealRow window uniform ->
            SemanticNameCert
                (fun row : BHist =>
                  CauchySequenceSpaceCarrier family schedule window tolerance completion
                    transport route name bundle pkg ∧ hsame row completion)
                (fun row : BHist =>
                  CauchySequenceSpaceCarrier family schedule window tolerance completion
                    transport route name bundle pkg ∧ hsame row completion)
                (fun row : BHist =>
                  CauchySequenceSpaceCarrier family schedule window tolerance completion
                    transport route name bundle pkg ∧ hsame row completion)
                hsame ∧
              UnaryHistory uniform ∧ Cont sealRow window uniform ∧
                PkgSig bundle route pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier routeToHandoff handoffToSeal sealToUniform
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
            name bundle pkg ∧ hsame row completion)
        (fun row : BHist =>
          CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
            name bundle pkg ∧ hsame row completion)
        (fun row : BHist =>
          CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
            name bundle pkg ∧ hsame row completion)
        hsame :=
    CauchySequenceSpaceCarrier_namecert_obligation_surface carrier
  obtain ⟨_familyUnary, _scheduleUnary, windowUnary, _toleranceUnary, completionUnary,
    _transportUnary, routeUnary, nameUnary, _familyRoute, _windowToleranceCompletion,
    _completionTransportRoute, routePkg, namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary nameUnary routeToHandoff
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed handoffUnary completionUnary handoffToSeal
  have uniformUnary : UnaryHistory uniform :=
    unary_cont_closed sealUnary windowUnary sealToUniform
  exact ⟨cert, uniformUnary, sealToUniform, routePkg, namePkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
