import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_bridge_tuple_audit_normal_form [AskSetup]
    [PackageSetup]
    {socket request gate ledger transport route provenance nameRow bridgeRead auditRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow bridgeRead →
        Cont bridgeRead provenance auditRead →
          PkgSig bundle bridgeRead pkg →
            PkgSig bundle auditRead pkg →
              SemanticNameCert
                    (fun row : BHist =>
                      ApophaticNameCarrier socket request gate ledger transport route provenance
                        nameRow bundle pkg ∧ hsame row nameRow)
                    (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ hsame row nameRow ∧
                        Cont ledger nameRow bridgeRead)
                    hsame ∧
                  UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
                  UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                  UnaryHistory provenance ∧ UnaryHistory nameRow ∧
                  UnaryHistory bridgeRead ∧ UnaryHistory auditRead ∧
                  Cont socket request gate ∧ Cont request gate route ∧
                  Cont gate ledger nameRow ∧ Cont ledger nameRow bridgeRead ∧
                  Cont bridgeRead provenance auditRead ∧ hsame ledger (append request gate) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg ∧
                  PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameBridge bridgeProvenanceAudit bridgePkg auditPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, _gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameBridge
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed bridgeUnary provenanceUnary bridgeProvenanceAudit
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row nameRow)
          (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ hsame row nameRow ∧
              Cont ledger nameRow bridgeRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro nameRow ⟨carrierPacket, hsame_refl nameRow⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameName : hsame row nameRow := source.right
      exact ⟨rowSameName, unary_transport nameRowUnary (hsame_symm rowSameName)⟩
    · intro row source
      exact ⟨provenancePkg, source.right, ledgerNameBridge⟩
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, bridgeUnary, auditUnary, socketRequestGate,
      requestGateRoute, gateLedgerNameRow, ledgerNameBridge, bridgeProvenanceAudit,
      ledgerSameRequestGate, provenancePkg, bridgePkg, auditPkg⟩

end BEDC.Derived.ApophaticNameUp
