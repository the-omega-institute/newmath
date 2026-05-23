import BEDC.Derived.CauchySequenceSpaceUp.WindowFactorization

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_finite_section_pullback_correspondence [AskSetup]
    [PackageSetup]
    {family schedule window tolerance completion transport route name handoff sealRow inventory
      sectionRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg →
      Cont route name handoff →
        Cont handoff completion sealRow →
          Cont sealRow route inventory →
            Cont inventory tolerance sectionRead →
              Cont sectionRead completion realSeal →
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
                  UnaryHistory sectionRead ∧ UnaryHistory realSeal ∧
                    Cont inventory tolerance sectionRead ∧
                      Cont sectionRead completion realSeal ∧ PkgSig bundle route pkg ∧
                        PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeToHandoff handoffToSeal sealToInventory inventoryToSection
    sectionToReal
  have tailFacts :
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
          hsame ∧
        UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory inventory ∧
          UnaryHistory sectionRead ∧ Cont route name handoff ∧
            Cont handoff completion sealRow ∧ Cont sealRow route inventory ∧
              Cont inventory tolerance sectionRead ∧ PkgSig bundle route pkg ∧
                PkgSig bundle name pkg :=
    CauchySequenceSpaceCarrier_tail_window_factorization carrier routeToHandoff handoffToSeal
      sealToInventory inventoryToSection
  obtain ⟨cert, _handoffUnary, _sealUnary, _inventoryUnary, sectionUnary, _routeToHandoff,
    _handoffToSeal, _sealToInventory, inventoryToSectionRow, routePkg, namePkg⟩ :=
    tailFacts
  obtain ⟨_familyUnary, _scheduleUnary, _windowUnary, _toleranceUnary, completionUnary,
    _transportUnary, _routeUnary, _nameUnary, _familyRoute, _completionRoute,
    _transportRoute, _routePkg, _namePkg⟩ := carrier
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed sectionUnary completionUnary sectionToReal
  exact
    ⟨cert, sectionUnary, realSealUnary, inventoryToSectionRow, sectionToReal, routePkg,
      namePkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
