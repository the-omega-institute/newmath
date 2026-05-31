import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceRealRegSeqRatNonescape [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName realRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg →
      Cont readback metric realRead →
        Cont realRead ledger sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory ledger ∧
              UnaryHistory realRead ∧ UnaryHistory sealRead ∧ Cont readback metric realRead ∧
                Cont realRead ledger sealRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: PolishspaceRootCauchyBasisCarrier BHist Cont ProbeBundle PkgSig
  intro carrier readbackMetricReal realLedgerSeal sealPkg
  obtain ⟨metricUnary, _completeUnary, _separableUnary, streamUnary, readbackUnary,
    ledgerUnary, _alignmentUnary, _transportUnary, _localNameUnary,
    _metricCompleteAlignment, _alignmentStreamReadback, _ledgerTransportRoute,
    provenancePkg⟩ := carrier
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary metricUnary readbackMetricReal
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed realUnary ledgerUnary realLedgerSeal
  exact
    ⟨streamUnary, readbackUnary, ledgerUnary, realUnary, sealUnary, readbackMetricReal,
      realLedgerSeal, provenancePkg, sealPkg⟩

end BEDC.Derived.PolishspaceUp
