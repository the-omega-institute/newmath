import BEDC.Derived.DependentCodomainClosurePreservationUp

namespace BEDC.Derived.DependentCodomainClosurePreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DependentCodomainClosurePreservationTransport [AskSetup] [PackageSetup]
    {pi domain arg reduced codomainSource codomainTarget betaClosed substClosed boundary
      transport ledger htrans replay provenance name downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DependentCodomainClosurePreservationPacket pi domain arg reduced codomainSource
        codomainTarget betaClosed substClosed boundary transport ledger htrans replay provenance
        name bundle pkg ->
      Cont transport ledger downstream ->
        SemanticNameCert
            (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row downstream ∧ Cont codomainSource codomainTarget transport)
            (fun row : BHist =>
              hsame row downstream ∧ Cont transport ledger downstream ∧
                PkgSig bundle provenance pkg)
            hsame ∧
          UnaryHistory codomainSource ∧ UnaryHistory codomainTarget ∧
            UnaryHistory betaClosed ∧ UnaryHistory substClosed ∧ UnaryHistory boundary ∧
              UnaryHistory transport ∧ UnaryHistory ledger ∧ UnaryHistory downstream ∧
                Cont codomainSource codomainTarget transport ∧
                  Cont betaClosed substClosed ledger ∧ Cont transport ledger downstream ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet downstreamRoute
  obtain ⟨_piUnary, _domainUnary, _argUnary, _reducedUnary, codomainSourceUnary,
    codomainTargetUnary, betaClosedUnary, substClosedUnary, boundaryUnary, transportUnary,
    ledgerUnary, _htransUnary, _replayUnary, _provenanceUnary, _nameUnary, _piDomainArg,
    _argReducedCodomainSource, codomainTransport, betaSubstLedger, _namePkg,
    provenancePkg⟩ := packet
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed transportUnary ledgerUnary downstreamRoute
  have sourceAtDownstream : hsame downstream downstream ∧ UnaryHistory downstream :=
    ⟨hsame_refl downstream, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row downstream ∧ Cont codomainSource codomainTarget transport)
          (fun row : BHist =>
            hsame row downstream ∧ Cont transport ledger downstream ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstream sourceAtDownstream
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
      exact ⟨source.left, codomainTransport⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, downstreamRoute, provenancePkg⟩
  }
  exact
    ⟨cert, codomainSourceUnary, codomainTargetUnary, betaClosedUnary, substClosedUnary,
      boundaryUnary, transportUnary, ledgerUnary, downstreamUnary, codomainTransport,
      betaSubstLedger, downstreamRoute, provenancePkg⟩

end BEDC.Derived.DependentCodomainClosurePreservationUp
