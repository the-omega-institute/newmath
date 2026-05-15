import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_source_citation_export [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citationRead requestRead
      gateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont route provenance citationRead →
        Cont request gate requestRead →
          Cont gate ledger gateRead →
            PkgSig bundle citationRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row provenance)
                  (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle citationRead pkg ∧
                      hsame row provenance ∧ Cont route provenance citationRead)
                  hsame ∧
                UnaryHistory citationRead ∧ UnaryHistory requestRead ∧
                  UnaryHistory gateRead ∧ Cont route provenance citationRead ∧
                    Cont request gate requestRead ∧ Cont gate ledger gateRead ∧
                      PkgSig bundle citationRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeProvenanceCitation requestGateRead gateLedgerRead citationPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ :=
    carrier
  have citationUnary : UnaryHistory citationRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCitation
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed requestUnary gateUnary requestGateRead
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row provenance)
          (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle citationRead pkg ∧
              hsame row provenance ∧ Cont route provenance citationRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro provenance ⟨carrierPacket, hsame_refl provenance⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameProvenance : hsame row provenance := source.right
      exact
        ⟨rowSameProvenance,
          unary_transport provenanceUnary (hsame_symm rowSameProvenance)⟩
    · intro _row source
      exact ⟨provenancePkg, citationPkg, source.right, routeProvenanceCitation⟩
  exact
    ⟨cert, citationUnary, requestReadUnary, gateReadUnary, routeProvenanceCitation,
      requestGateRead, gateLedgerRead, citationPkg⟩

end BEDC.Derived.ApophaticNameUp
