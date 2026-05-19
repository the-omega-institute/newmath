import BEDC.Derived.ApophaticNameUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameDownstreamBoundaryConsumer [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow boundaryRead consumerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow boundaryRead →
        Cont boundaryRead route consumerRead →
          PkgSig bundle consumerRead pkg →
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory nameRow ∧ UnaryHistory boundaryRead ∧
                UnaryHistory consumerRead ∧ Cont socket request gate ∧
                  Cont gate ledger nameRow ∧ Cont ledger nameRow boundaryRead ∧
                    Cont boundaryRead route consumerRead ∧ hsame ledger (append request gate) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier boundaryRoute consumerRoute consumerPkg
  rcases carrier with
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
      _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed ledgerUnary nameRowUnary boundaryRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed boundaryUnary routeUnary consumerRoute
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, nameRowUnary, boundaryUnary,
      consumerUnary, socketRequestGate, gateLedgerNameRow, boundaryRoute, consumerRoute,
      ledgerSameRequestGate, provenancePkg, consumerPkg⟩

theorem ApophaticNameCarrier_downstream_boundary_consumer [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow consumerRead boundaryRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow consumerRead →
        Cont consumerRead provenance boundaryRead →
          PkgSig bundle boundaryRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row boundaryRead)
                (fun row : BHist =>
                  hsame row boundaryRead ∧ UnaryHistory row ∧
                    Cont consumerRead provenance boundaryRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg ∧
                    hsame row boundaryRead)
                hsame ∧
              UnaryHistory consumerRead ∧ UnaryHistory boundaryRead ∧
                Cont ledger nameRow consumerRead ∧
                  Cont consumerRead provenance boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameConsumer consumerProvenanceBoundary boundaryPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameConsumer
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed consumerUnary provenanceUnary consumerProvenanceBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row boundaryRead)
          (fun row : BHist =>
            hsame row boundaryRead ∧ UnaryHistory row ∧
              Cont consumerRead provenance boundaryRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg ∧
              hsame row boundaryRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro boundaryRead ⟨carrierPacket, hsame_refl boundaryRead⟩
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
          consumerProvenanceBoundary⟩
    · intro _row source
      exact ⟨provenancePkg, boundaryPkg, source.right⟩
  exact
    ⟨cert, consumerUnary, boundaryUnary, ledgerNameConsumer, consumerProvenanceBoundary⟩

end BEDC.Derived.ApophaticNameUp
