import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_downstream_refusal_ledger_exhaustion
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead
      ledgerAudit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow downstreamRead →
        Cont downstreamRead route ledgerAudit →
          PkgSig bundle ledgerAudit pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route
                    provenance nameRow bundle pkg ∧ hsame row ledgerAudit)
                (fun row : BHist =>
                  hsame row ledgerAudit ∧ UnaryHistory row ∧
                    Cont downstreamRead route ledgerAudit)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerAudit pkg ∧
                    hsame row ledgerAudit)
                hsame ∧
              UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
                UnaryHistory ledger ∧ UnaryHistory downstreamRead ∧
                  UnaryHistory ledgerAudit ∧ Cont socket request gate ∧
                    Cont ledger nameRow downstreamRead ∧
                      Cont downstreamRead route ledgerAudit ∧
                        hsame ledger (append request gate) ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerAudit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameDownstream downstreamRouteAudit auditPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameDownstream
  have ledgerAuditUnary : UnaryHistory ledgerAudit :=
    unary_cont_closed downstreamUnary routeUnary downstreamRouteAudit
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row ledgerAudit)
          (fun row : BHist =>
            hsame row ledgerAudit ∧ UnaryHistory row ∧
              Cont downstreamRead route ledgerAudit)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerAudit pkg ∧
              hsame row ledgerAudit)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro ledgerAudit ⟨carrierPacket, hsame_refl ledgerAudit⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport ledgerAuditUnary (hsame_symm source.right),
            downstreamRouteAudit⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, auditPkg, source.right⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, downstreamUnary,
      ledgerAuditUnary, socketRequestGate, ledgerNameDownstream, downstreamRouteAudit,
      ledgerSameRequestGate, provenancePkg, auditPkg⟩

end BEDC.Derived.ApophaticNameUp
