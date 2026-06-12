import BEDC.Derived.SequentiallyCompleteMetricUp.NameCertObligations

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricRegSeqRatSourceRoute [AskSetup] [PackageSetup]
    {source stream modulus limit ledger transport replay provenance localName readback :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentiallyCompleteMetricCarrier source stream modulus limit ledger transport replay
        provenance localName bundle pkg →
      UnaryHistory readback →
        Cont stream readback ledger →
          UnaryHistory source ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
            UnaryHistory modulus ∧ UnaryHistory limit ∧ UnaryHistory ledger ∧
              Cont stream readback ledger ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier readbackUnary readbackRoute
  obtain ⟨sourceUnary, streamUnary, modulusUnary, limitUnary, ledgerUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _sourceStreamReplay,
    _replayLimitLedger, _transportLocalName, provenancePkg⟩ := carrier
  exact
    ⟨sourceUnary, streamUnary, readbackUnary, modulusUnary, limitUnary, ledgerUnary,
      readbackRoute, provenancePkg⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
