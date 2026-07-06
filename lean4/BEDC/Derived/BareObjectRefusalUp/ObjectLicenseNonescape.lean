import BEDC.Derived.BareObjectRefusalUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BareObjectRefusalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BareObjectRefusalCarrier
    (objectName missingFields refusal witnessAudit ledger transport routes provenance
      localName : BHist) :
    Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory objectName ∧ UnaryHistory missingFields ∧ UnaryHistory refusal ∧
    UnaryHistory witnessAudit ∧ UnaryHistory ledger ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont missingFields refusal witnessAudit ∧ Cont routes provenance localName

theorem BareObjectRefusalCarrier_object_license_nonescape
    {objectName missingFields refusal witnessAudit ledger transport routes provenance
      localName : BHist} :
    BareObjectRefusalCarrier objectName missingFields refusal witnessAudit ledger transport
        routes provenance localName ->
      UnaryHistory objectName ∧ UnaryHistory missingFields ∧ UnaryHistory refusal ∧
        UnaryHistory witnessAudit ∧ UnaryHistory ledger ∧
          Cont missingFields refusal witnessAudit ∧ Cont routes provenance localName := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier
  obtain ⟨objectUnary, missingUnary, refusalUnary, witnessUnary, ledgerUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _localNameUnary, witnessRoute,
    localNameRoute⟩ := carrier
  exact
    ⟨objectUnary, missingUnary, refusalUnary, witnessUnary, ledgerUnary, witnessRoute,
      localNameRoute⟩

end BEDC.Derived.BareObjectRefusalUp
