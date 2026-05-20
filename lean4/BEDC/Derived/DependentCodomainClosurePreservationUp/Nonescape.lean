import BEDC.Derived.DependentCodomainClosurePreservationUp

namespace BEDC.Derived.DependentCodomainClosurePreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DependentCodomainClosurePreservationNonescape [AskSetup] [PackageSetup]
    {pi domain arg reduced codomainSource codomainTarget betaClosed substClosed boundary
      transport ledger htrans replay provenance name attempted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DependentCodomainClosurePreservationPacket pi domain arg reduced codomainSource
        codomainTarget betaClosed substClosed boundary transport ledger htrans replay provenance
        name bundle pkg →
      Cont replay ledger attempted →
        PkgSig bundle attempted pkg →
          SemanticNameCert
              (fun row : BHist => hsame row attempted ∧ UnaryHistory row)
              (fun row : BHist => hsame row attempted ∧ Cont replay ledger attempted)
              (fun row : BHist => hsame row attempted ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory attempted ∧ Cont replay ledger attempted ∧
              PkgSig bundle attempted pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet replayLedger attemptedPkg
  obtain ⟨_piUnary, _domainUnary, _argUnary, _reducedUnary, _codomainSourceUnary,
    _codomainTargetUnary, _betaClosedUnary, _substClosedUnary, _boundaryUnary, _transportUnary,
    ledgerUnary, _htransUnary, replayUnary, _provenanceUnary, _nameUnary, _piDomainArg,
    _argReducedCodomainSource, _codomainSourceTargetTransport, _betaSubstLedger, _namePkg,
    provenancePkg⟩ := packet
  have attemptedUnary : UnaryHistory attempted :=
    unary_cont_closed replayUnary ledgerUnary replayLedger
  have sourceAttempted :
      (fun row : BHist => hsame row attempted ∧ UnaryHistory row) attempted := by
    exact ⟨hsame_refl attempted, attemptedUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row attempted ∧ UnaryHistory row)
        (fun row : BHist => hsame row attempted ∧ Cont replay ledger attempted)
        (fun row : BHist => hsame row attempted ∧ PkgSig bundle provenance pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro attempted sourceAttempted
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, replayLedger⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg⟩
    }
  exact ⟨cert, attemptedUnary, replayLedger, attemptedPkg, provenancePkg⟩

end BEDC.Derived.DependentCodomainClosurePreservationUp
