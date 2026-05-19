import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ScientificModelBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ScientificModelBridgeCarrier [AskSetup] [PackageSetup]
    (object audit bridge modelAudit openFit ledger prediction transport hsameRow contRow
      provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory object ∧ UnaryHistory audit ∧ UnaryHistory bridge ∧
    UnaryHistory modelAudit ∧ UnaryHistory openFit ∧ UnaryHistory ledger ∧
      UnaryHistory prediction ∧ UnaryHistory transport ∧ UnaryHistory hsameRow ∧
        UnaryHistory contRow ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont object audit bridge ∧ Cont bridge modelAudit openFit ∧
            Cont ledger prediction transport ∧ Cont hsameRow contRow provenance ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem ScientificModelBridgeCarrier_falsifiable_prediction [AskSetup] [PackageSetup]
    {object audit bridge modelAudit openFit ledger prediction transport hsameRow contRow
      provenance name ledgerRead predictionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ScientificModelBridgeCarrier object audit bridge modelAudit openFit ledger prediction
        transport hsameRow contRow provenance name bundle pkg →
      Cont ledger prediction ledgerRead →
        Cont ledgerRead transport predictionRead →
          PkgSig bundle predictionRead pkg →
            UnaryHistory ledger ∧ UnaryHistory prediction ∧ UnaryHistory ledgerRead ∧
              UnaryHistory predictionRead ∧ Cont ledger prediction ledgerRead ∧
                Cont ledgerRead transport predictionRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle predictionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier ledgerPredictionRead ledgerReadTransportPredictionRead predictionPkg
  obtain ⟨_objectUnary, _auditUnary, _bridgeUnary, _modelAuditUnary, _openFitUnary,
    ledgerUnary, predictionUnary, transportUnary, _hsameRowUnary, _contRowUnary,
    _provenanceUnary, _nameUnary, _objectAuditBridge, _bridgeModelAuditOpenFit,
    _ledgerPredictionTransport, _hsameContProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary predictionUnary ledgerPredictionRead
  have predictionReadUnary : UnaryHistory predictionRead :=
    unary_cont_closed ledgerReadUnary transportUnary ledgerReadTransportPredictionRead
  exact
    ⟨ledgerUnary,
      predictionUnary,
      ledgerReadUnary,
      predictionReadUnary,
      ledgerPredictionRead,
      ledgerReadTransportPredictionRead,
      provenancePkg,
      predictionPkg⟩

end BEDC.Derived.ScientificModelBridgeUp
