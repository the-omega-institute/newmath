import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ScientificModelBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem ScientificModelBridgeCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {object audit bridge modelAudit openFit ledger prediction transport hsameRow contRow
      provenance name predictionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ScientificModelBridgeCarrier object audit bridge modelAudit openFit ledger prediction
        transport hsameRow contRow provenance name bundle pkg →
      Cont ledger prediction predictionRead →
        PkgSig bundle predictionRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ScientificModelBridgeCarrier object audit bridge modelAudit openFit ledger
                    prediction transport hsameRow contRow provenance name bundle pkg ∧
                  (hsame row ledger ∨ hsame row predictionRead ∨ hsame row name))
              (fun _row : BHist => Cont ledger prediction predictionRead)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle predictionRead pkg)
              hsame ∧
            UnaryHistory ledger ∧ UnaryHistory prediction ∧ UnaryHistory predictionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier predictionRoute predictionPkg
  have carrierWitness := carrier
  obtain ⟨_objectUnary, _auditUnary, _bridgeUnary, _modelAuditUnary, _openFitUnary,
    ledgerUnary, predictionUnary, _transportUnary, _hsameRowUnary, _contRowUnary,
    _provenanceUnary, nameUnary, _objectAuditBridge, _bridgeModelAuditOpenFit,
    _ledgerPredictionTransport, _hsameContProvenance, _provenancePkg, _namePkg⟩ :=
    carrier
  have predictionReadUnary : UnaryHistory predictionRead :=
    unary_cont_closed ledgerUnary predictionUnary predictionRoute
  have carrierInhabited :
      Exists
        (fun row : BHist =>
          ScientificModelBridgeCarrier object audit bridge modelAudit openFit ledger
              prediction transport hsameRow contRow provenance name bundle pkg ∧
            (hsame row ledger ∨ hsame row predictionRead ∨ hsame row name)) :=
    Exists.intro predictionRead
      ⟨carrierWitness, Or.inr (Or.inl (hsame_refl predictionRead))⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ScientificModelBridgeCarrier object audit bridge modelAudit openFit ledger
                prediction transport hsameRow contRow provenance name bundle pkg ∧
              (hsame row ledger ∨ hsame row predictionRead ∨ hsame row name))
          (fun _row : BHist => Cont ledger prediction predictionRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle predictionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := carrierInhabited
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows source
        cases source with
        | intro carrierSource sourceRead =>
            refine ⟨carrierSource, ?_⟩
            cases sourceRead with
            | inl sameLedger =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameLedger)
            | inr rest =>
                cases rest with
                | inl samePrediction =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) samePrediction))
                | inr sameName =>
                    exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameName))
    }
    pattern_sound := by
      intro _row _source
      exact predictionRoute
    ledger_sound := by
      intro row source
      cases source with
      | intro _carrierSource sourceRead =>
          cases sourceRead with
          | inl sameLedger =>
              exact ⟨unary_transport ledgerUnary (hsame_symm sameLedger), predictionPkg⟩
          | inr rest =>
              cases rest with
              | inl samePrediction =>
                  exact
                    ⟨unary_transport predictionReadUnary (hsame_symm samePrediction),
                      predictionPkg⟩
              | inr sameName =>
                  exact ⟨unary_transport nameUnary (hsame_symm sameName), predictionPkg⟩
  }
  exact ⟨cert, ledgerUnary, predictionUnary, predictionReadUnary⟩

end BEDC.Derived.ScientificModelBridgeUp
