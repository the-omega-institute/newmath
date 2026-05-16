import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_audit_package [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger provenance auditRead ->
        PkgSig bundle auditRead pkg ->
          UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory nameRow ∧ UnaryHistory auditRead ∧
                Cont socket request gate ∧ Cont request gate route ∧
                  Cont gate ledger route ∧ Cont gate ledger nameRow ∧
                    Cont ledger provenance auditRead ∧ hsame ledger (append request gate) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
                        SemanticNameCert
                          (fun row : BHist =>
                            ApophaticNameCarrier socket request gate ledger transport route
                              provenance nameRow bundle pkg ∧ hsame row ledger)
                          (fun row : BHist =>
                            hsame row ledger ∧ UnaryHistory row ∧
                              Cont ledger provenance auditRead)
                          (fun row : BHist =>
                            PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
                              hsame row ledger)
                          hsame := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerProvenanceAudit auditPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed ledgerUnary provenanceUnary ledgerProvenanceAudit
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
            bundle pkg ∧ hsame row ledger)
        (fun row : BHist =>
          hsame row ledger ∧ UnaryHistory row ∧ Cont ledger provenance auditRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧ hsame row ledger)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro ledger (And.intro carrierPacket (hsame_refl ledger))
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
          exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport ledgerUnary (hsame_symm source.right),
            ledgerProvenanceAudit⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, auditPkg, source.right⟩
    }
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, auditUnary, socketRequestGate, requestGateRoute,
      gateLedgerRoute, gateLedgerNameRow, ledgerProvenanceAudit, ledgerSameRequestGate,
      provenancePkg, auditPkg, cert⟩

end BEDC.Derived.ApophaticNameUp
