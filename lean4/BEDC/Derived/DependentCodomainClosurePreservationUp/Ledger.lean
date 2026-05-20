import BEDC.Derived.DependentCodomainClosurePreservationUp.Transport

namespace BEDC.Derived.DependentCodomainClosurePreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DependentCodomainClosurePreservationLedger [AskSetup] [PackageSetup]
    {pi domain arg reduced codomainSource codomainTarget betaClosed substClosed boundary
      transport ledger htrans replay provenance name downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DependentCodomainClosurePreservationPacket pi domain arg reduced codomainSource
        codomainTarget betaClosed substClosed boundary transport ledger htrans replay provenance
        name bundle pkg →
      Cont transport ledger downstream →
        SemanticNameCert
            (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
            (fun _row : BHist =>
              Cont codomainSource codomainTarget transport ∧ Cont transport ledger downstream)
            (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row downstream)
            hsame ∧
          UnaryHistory ledger ∧ UnaryHistory downstream ∧ Cont betaClosed substClosed ledger ∧
            Cont transport ledger downstream ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg
  intro packet downstreamRoute
  obtain ⟨_piUnary, _domainUnary, _argUnary, _reducedUnary, _codomainSourceUnary,
    _codomainTargetUnary, _betaClosedUnary, _substClosedUnary, _boundaryUnary, transportUnary,
    ledgerUnary, _htransUnary, _replayUnary, _provenanceUnary, _nameUnary, _piDomainArg,
    _argReducedCodomainSource, codomainTransport, betaSubstLedger, _namePkg,
    provenancePkg⟩ := packet
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed transportUnary ledgerUnary downstreamRoute
  have sourceAtDownstream :
      (fun row : BHist => hsame row downstream ∧ UnaryHistory row) downstream :=
    ⟨hsame_refl downstream, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont codomainSource codomainTarget transport ∧ Cont transport ledger downstream)
          (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row downstream)
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
      intro _row _source
      exact ⟨codomainTransport, downstreamRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source.left⟩
  }
  exact ⟨cert, ledgerUnary, downstreamUnary, betaSubstLedger, downstreamRoute, provenancePkg⟩

end BEDC.Derived.DependentCodomainClosurePreservationUp
