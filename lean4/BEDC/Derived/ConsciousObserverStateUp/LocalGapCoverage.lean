import BEDC.Derived.ConsciousObserverStateUp

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousObserverStateCarrier_local_gap_coverage [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance name endpoint gapRead
      ledgerRead coverageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        name endpoint bundle pkg →
      Cont ledger gap gapRead →
        Cont recognition ledgerRead coverageRead →
          hsame ledgerRead ledger →
            PkgSig bundle coverageRead pkg →
              SemanticNameCert
                    (fun row : BHist =>
                      ConsciousObserverStateCarrier observer state recognition ledger gap
                          transport route provenance name endpoint bundle pkg ∧
                        (hsame row ledger ∨ hsame row gap))
                    (fun row : BHist =>
                      ((hsame row ledger ∧ UnaryHistory ledgerRead) ∨
                          (hsame row gap ∧ Cont ledger gap gapRead)) ∧
                        Cont recognition ledger gap)
                    (fun _row : BHist =>
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle coverageRead pkg ∧
                        hsame ledgerRead ledger ∧ Cont recognition ledgerRead coverageRead)
                    hsame ∧
                UnaryHistory gapRead ∧ UnaryHistory coverageRead ∧ hsame coverageRead gap ∧
                  Cont ledger gap gapRead ∧ Cont recognition ledgerRead coverageRead ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle coverageRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerGapRead recognitionLedgerReadCoverage sameLedgerReadLedger coveragePkg
  have carrierWitness :
      ConsciousObserverStateCarrier observer state recognition ledger gap transport route
        provenance name endpoint bundle pkg :=
    carrier
  obtain ⟨_observerUnary, _stateUnary, recognitionUnary, ledgerUnary, gapUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _endpointUnary,
    _observerRouteEndpoint, _stateRouteEndpoint, recognitionLedgerGap,
    _transportProvenanceEndpoint, endpointPkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_transport_symm ledgerUnary sameLedgerReadLedger
  have gapReadUnary : UnaryHistory gapRead :=
    unary_cont_closed ledgerUnary gapUnary ledgerGapRead
  have coverageReadUnary : UnaryHistory coverageRead :=
    unary_cont_closed recognitionUnary ledgerReadUnary recognitionLedgerReadCoverage
  have coverageSameGap : hsame coverageRead gap :=
    cont_respects_hsame (hsame_refl recognition) sameLedgerReadLedger
      recognitionLedgerReadCoverage recognitionLedgerGap
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ConsciousObserverStateCarrier observer state recognition ledger gap transport route
                provenance name endpoint bundle pkg ∧
              (hsame row ledger ∨ hsame row gap))
          (fun row : BHist =>
            ((hsame row ledger ∧ UnaryHistory ledgerRead) ∨
                (hsame row gap ∧ Cont ledger gap gapRead)) ∧
              Cont recognition ledger gap)
          (fun _row : BHist =>
            PkgSig bundle endpoint pkg ∧ PkgSig bundle coverageRead pkg ∧
              hsame ledgerRead ledger ∧ Cont recognition ledgerRead coverageRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger
          ⟨carrierWitness, Or.inl (hsame_refl ledger)⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _row' same
        exact hsame_symm same
      · intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        rcases source.right with rowLedger | rowGap
        · exact
            ⟨source.left, Or.inl (hsame_trans (hsame_symm same) rowLedger)⟩
        · exact
            ⟨source.left, Or.inr (hsame_trans (hsame_symm same) rowGap)⟩
    · intro row source
      rcases source.right with rowLedger | rowGap
      · exact
          ⟨Or.inl ⟨rowLedger, ledgerReadUnary⟩, recognitionLedgerGap⟩
      · exact
          ⟨Or.inr ⟨rowGap, ledgerGapRead⟩, recognitionLedgerGap⟩
    · intro _row _source
      exact
        ⟨endpointPkg, coveragePkg, sameLedgerReadLedger, recognitionLedgerReadCoverage⟩
  exact
    ⟨cert, gapReadUnary, coverageReadUnary, coverageSameGap, ledgerGapRead,
      recognitionLedgerReadCoverage, endpointPkg, coveragePkg⟩

end BEDC.Derived.ConsciousObserverStateUp
