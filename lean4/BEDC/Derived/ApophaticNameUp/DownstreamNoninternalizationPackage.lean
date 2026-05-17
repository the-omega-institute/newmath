import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_downstream_noninternalization_package [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstream boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      Cont route provenance downstream →
        Cont downstream nameRow boundary →
          PkgSig bundle boundary pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row downstream)
                (fun row : BHist =>
                  hsame row downstream ∧ UnaryHistory row ∧
                    Cont route provenance downstream)
                (fun _row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle boundary pkg ∧
                    Cont downstream nameRow boundary)
                hsame ∧
              UnaryHistory downstream ∧ UnaryHistory boundary ∧
                Cont route provenance downstream ∧ Cont downstream nameRow boundary ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeProvenanceDownstream downstreamNameBoundary boundaryPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceDownstream
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed downstreamUnary nameRowUnary downstreamNameBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row downstream)
          (fun row : BHist =>
            hsame row downstream ∧ UnaryHistory row ∧
              Cont route provenance downstream)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle boundary pkg ∧
              Cont downstream nameRow boundary)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro downstream ⟨carrierPacket, hsame_refl downstream⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact
        ⟨source.right, unary_transport downstreamUnary (hsame_symm source.right),
          routeProvenanceDownstream⟩
    · intro _row _source
      exact ⟨provenancePkg, boundaryPkg, downstreamNameBoundary⟩
  exact
    ⟨cert, downstreamUnary, boundaryUnary, routeProvenanceDownstream,
      downstreamNameBoundary, ledgerSameRequestGate, provenancePkg, boundaryPkg⟩

end BEDC.Derived.ApophaticNameUp
