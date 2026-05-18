import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_downstream_named_externality_refusal [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citation boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow citation →
        Cont citation provenance boundary →
          PkgSig bundle boundary pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row boundary)
                (fun row : BHist =>
                  hsame row boundary ∧ UnaryHistory row ∧ Cont citation provenance boundary)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle boundary pkg ∧
                    hsame row boundary)
                hsame ∧
              UnaryHistory citation ∧ UnaryHistory boundary ∧
                Cont ledger nameRow citation ∧ Cont citation provenance boundary := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameCitation citationProvenanceBoundary boundaryPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have citationUnary : UnaryHistory citation :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameCitation
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed citationUnary provenanceUnary citationProvenanceBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row boundary)
          (fun row : BHist =>
            hsame row boundary ∧ UnaryHistory row ∧ Cont citation provenance boundary)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle boundary pkg ∧
              hsame row boundary)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro boundary ⟨carrierPacket, hsame_refl boundary⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact
        ⟨source.right, unary_transport boundaryUnary (hsame_symm source.right),
          citationProvenanceBoundary⟩
    · intro _row source
      exact ⟨provenancePkg, boundaryPkg, source.right⟩
  exact
    ⟨cert, citationUnary, boundaryUnary, ledgerNameCitation, citationProvenanceBoundary⟩

end BEDC.Derived.ApophaticNameUp
