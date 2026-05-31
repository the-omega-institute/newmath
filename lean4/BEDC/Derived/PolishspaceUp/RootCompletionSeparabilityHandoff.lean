import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceRootCompletionSeparabilityHandoff [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName completionRead separableRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg →
      Cont metric complete completionRead →
        Cont metric separable separableRead →
          Cont completionRead separableRead handoffRead →
            PkgSig bundle handoffRead pkg →
              UnaryHistory metric ∧ UnaryHistory complete ∧ UnaryHistory separable ∧
                UnaryHistory completionRead ∧ UnaryHistory separableRead ∧
                  UnaryHistory handoffRead ∧ Cont metric complete completionRead ∧
                    Cont metric separable separableRead ∧
                      Cont completionRead separableRead handoffRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier metricCompleteRead metricSeparableRead completionSeparableHandoff handoffPkg
  rcases carrier with
    ⟨metricUnary, completeUnary, separableUnary, _streamUnary, _readbackUnary, _ledgerUnary,
      _alignmentUnary, _transportUnary, _localNameUnary, _metricCompleteAlignment,
      _alignmentStreamReadback, _ledgerTransportRoute, provenancePkg⟩
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricCompleteRead
  have separableReadUnary : UnaryHistory separableRead :=
    unary_cont_closed metricUnary separableUnary metricSeparableRead
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed completionUnary separableReadUnary completionSeparableHandoff
  exact
    ⟨metricUnary, completeUnary, separableUnary, completionUnary, separableReadUnary,
      handoffUnary, metricCompleteRead, metricSeparableRead, completionSeparableHandoff,
      provenancePkg, handoffPkg⟩

end BEDC.Derived.PolishspaceUp
