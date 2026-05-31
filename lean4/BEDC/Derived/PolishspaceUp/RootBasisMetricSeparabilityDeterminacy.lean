import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceRootBasisMetricSeparabilityDeterminacy [AskSetup] [PackageSetup]
    {metric complete complete' separable separable' stream readback ledger ledger' alignment
      transport route provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg →
      PolishspaceRootCauchyBasisCarrier metric complete' separable' stream readback ledger'
          alignment transport route provenance localName bundle pkg →
        ∃ sourceRead : BHist, ∃ targetRead : BHist,
          UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧ hsame sourceRead targetRead ∧
            hsame sourceRead (append (append metric stream) readback) ∧
              hsame targetRead (append (append metric stream) readback) ∧
                Cont metric complete alignment ∧ Cont metric complete' alignment ∧
                  Cont alignment stream readback ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro sourceCarrier targetCarrier
  rcases sourceCarrier with
    ⟨metricUnary, _completeUnary, _separableUnary, streamUnary, readbackUnary,
      _ledgerUnary, _alignmentUnary, _transportUnary, _localNameUnary,
      metricCompleteAlignment, alignmentStreamReadback, _ledgerTransportRoute,
      provenancePkg⟩
  rcases targetCarrier with
    ⟨_metricUnary', _completeUnary', _separableUnary', _streamUnary', _readbackUnary',
      _ledgerUnary', _alignmentUnary', _transportUnary', _localNameUnary',
      metricCompleteAlignment', _alignmentStreamReadback', _ledgerTransportRoute',
      _provenancePkg'⟩
  let sharedRead : BHist := append (append metric stream) readback
  have metricStreamUnary : UnaryHistory (append metric stream) :=
    unary_append_closed metricUnary streamUnary
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_append_closed metricStreamUnary readbackUnary
  exact
    ⟨sharedRead, sharedRead, sharedReadUnary, sharedReadUnary, hsame_refl sharedRead,
      hsame_refl sharedRead, hsame_refl sharedRead, metricCompleteAlignment,
      metricCompleteAlignment', alignmentStreamReadback, provenancePkg⟩

end BEDC.Derived.PolishspaceUp
