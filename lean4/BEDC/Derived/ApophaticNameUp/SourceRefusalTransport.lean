import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_source_refusal_transport [AskSetup] [PackageSetup]
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
                      Cont ledger' nameRow' transportedRead →
                        PkgSig bundle provenance' pkg →
                          PkgSig bundle transportedRead pkg →
                            SemanticNameCert
                                (fun row : BHist =>
                                  ApophaticNameCarrier socket' request' gate' ledger'
                                    transport' route' provenance' nameRow' bundle pkg ∧
                                    hsame row transportedRead)
                                (fun row : BHist =>
                                  hsame row transportedRead ∧ UnaryHistory row ∧
                                    Cont ledger' nameRow' transportedRead)
                                (fun row : BHist =>
                                  PkgSig bundle provenance' pkg ∧
                                    PkgSig bundle transportedRead pkg ∧
                                      hsame row transportedRead)
                                hsame ∧
                              UnaryHistory socket' ∧ UnaryHistory request' ∧
                                UnaryHistory gate' ∧ UnaryHistory ledger' ∧
                                  UnaryHistory transportedRead ∧ Cont socket' request' gate' ∧
                                    Cont gate' ledger' nameRow' ∧
                                      Cont ledger' nameRow' transportedRead ∧
                                        hsame ledger' (append request' gate') ∧
                                          PkgSig bundle provenance' pkg ∧
                                            PkgSig bundle transportedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sameSocket sameRequest sameGate sameLedger sameTransport sameRoute
    sameProvenance sameNameRow ledgerNameTransported provenancePkg' transportedPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute, _gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, _provenancePkg⟩ := carrier
  cases sameSocket
  cases sameRequest
  cases sameGate
  cases sameLedger
  cases sameTransport
  cases sameRoute
  cases sameProvenance
  cases sameNameRow
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameTransported
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute, _gateLedgerRoute,
      gateLedgerNameRow, ledgerSameRequestGate, provenancePkg'⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row transportedRead)
          (fun row : BHist =>
            hsame row transportedRead ∧ UnaryHistory row ∧
              Cont ledger nameRow transportedRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle transportedRead pkg ∧
              hsame row transportedRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro transportedRead ⟨carrierPacket, hsame_refl transportedRead⟩
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
          ⟨source.right, unary_transport transportedUnary (hsame_symm source.right),
            ledgerNameTransported⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg', transportedPkg, source.right⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, transportedUnary,
      socketRequestGate, gateLedgerNameRow, ledgerNameTransported, ledgerSameRequestGate,
      provenancePkg', transportedPkg⟩

end BEDC.Derived.ApophaticNameUp
