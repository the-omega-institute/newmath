import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_classifier_stability [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socket' request' gate'
      ledger' transport' route' provenance' nameRow' classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      hsame socket socket' -> hsame request request' -> hsame gate gate' ->
        hsame ledger ledger' -> hsame transport transport' -> hsame route route' ->
          hsame provenance provenance' -> hsame nameRow nameRow' ->
            PkgSig bundle provenance' pkg -> Cont ledger' nameRow' classifierRead ->
              PkgSig bundle classifierRead pkg ->
                SemanticNameCert
                  (fun row : BHist => ApophaticNameCarrier socket' request' gate' ledger'
                    transport' route' provenance' nameRow' bundle pkg ∧ hsame row ledger')
                  (fun row : BHist => hsame row (append request' gate') ∧ UnaryHistory row)
                  (fun row : BHist => PkgSig bundle provenance' pkg ∧
                    hsame row (append request' gate') ∧ Cont gate' ledger' nameRow')
                  hsame ∧
                UnaryHistory classifierRead ∧ Cont ledger' nameRow' classifierRead ∧
                  hsame ledger' (append request' gate') ∧ PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sameSocket sameRequest sameGate sameLedger sameTransport sameRoute
    sameProvenance sameNameRow provenancePkg' ledgerNameClassifier classifierPkg
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
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameClassifier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
            bundle pkg ∧ hsame row ledger)
        (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ hsame row (append request gate) ∧
            Cont gate ledger nameRow)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro ledger ⟨carrierPacket, hsame_refl ledger⟩
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
          ⟨hsame_trans source.right ledgerSameRequestGate,
            unary_transport ledgerUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg', hsame_trans source.right ledgerSameRequestGate, gateLedgerNameRow⟩
    }
  exact ⟨cert, classifierUnary, ledgerNameClassifier, ledgerSameRequestGate, classifierPkg⟩

end BEDC.Derived.ApophaticNameUp
