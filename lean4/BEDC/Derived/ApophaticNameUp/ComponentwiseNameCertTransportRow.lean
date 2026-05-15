import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_componentwise_namecert_transport_row
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socket' request' gate'
      ledger' transport' route' provenance' nameRow' transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      hsame socket socket' →
        hsame request request' →
          hsame gate gate' →
            hsame ledger ledger' →
              hsame transport transport' →
                hsame route route' →
                  hsame provenance provenance' →
                    hsame nameRow nameRow' →
                      Cont ledger nameRow transportedRead →
                        PkgSig bundle provenance' pkg →
                          SemanticNameCert
                              (fun row : BHist =>
                                ApophaticNameCarrier socket' request' gate' ledger'
                                  transport' route' provenance' nameRow' bundle pkg ∧
                                  hsame row nameRow')
                              (fun row : BHist =>
                                hsame row nameRow' ∧ UnaryHistory row ∧
                                  Cont gate' ledger' nameRow')
                              (fun row : BHist =>
                                PkgSig bundle provenance' pkg ∧ hsame row nameRow' ∧
                                  Cont ledger nameRow transportedRead)
                              hsame ∧
                            ApophaticNameCarrier socket' request' gate' ledger' transport'
                              route' provenance' nameRow' bundle pkg ∧
                              hsame ledger' (append request' gate') ∧
                                Cont gate' ledger' nameRow' := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sameSocket sameRequest sameGate sameLedger sameTransport sameRoute
    sameProvenance sameNameRow ledgerNameTransported provenancePkg'
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, _provenancePkg⟩ := carrier
  cases sameSocket
  cases sameRequest
  cases sameGate
  cases sameLedger
  cases sameTransport
  cases sameRoute
  cases sameProvenance
  cases sameNameRow
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
      gateLedgerNameRow, ledgerSameRequestGate, provenancePkg'⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row nameRow)
          (fun row : BHist =>
            hsame row nameRow ∧ UnaryHistory row ∧ Cont gate ledger nameRow)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ hsame row nameRow ∧
              Cont ledger nameRow transportedRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro nameRow ⟨carrierPacket, hsame_refl nameRow⟩
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
          ⟨source.right, unary_transport nameRowUnary (hsame_symm source.right),
            gateLedgerNameRow⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg', source.right, ledgerNameTransported⟩
    }
  exact ⟨cert, carrierPacket, ledgerSameRequestGate, gateLedgerNameRow⟩

end BEDC.Derived.ApophaticNameUp
