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

theorem PolishspaceStreamnameRealDependencyAnchor [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      metricRead completionRead denseRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory complete →
        UnaryHistory separable →
          UnaryHistory stream →
            UnaryHistory readback →
              UnaryHistory ledger →
                UnaryHistory transport →
                  Cont metric stream metricRead →
                    Cont complete stream completionRead →
                      Cont separable stream denseRead →
                        Cont ledger transport replay →
                          Cont replay readback realRead →
                            PkgSig bundle provenance pkg →
                              PkgSig bundle localName pkg →
                                UnaryHistory stream ∧ UnaryHistory readback ∧
                                  UnaryHistory metricRead ∧ UnaryHistory completionRead ∧
                                    UnaryHistory denseRead ∧ UnaryHistory realRead ∧
                                      Cont metric stream metricRead ∧
                                        Cont complete stream completionRead ∧
                                          Cont separable stream denseRead ∧
                                            Cont replay readback realRead ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro metricUnary completeUnary separableUnary streamUnary readbackUnary ledgerUnary
    transportUnary metricStreamRead completeStreamRead separableStreamRead ledgerTransportReplay
    replayReadbackReal provenancePkg localNamePkg
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed metricUnary streamUnary metricStreamRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed completeUnary streamUnary completeStreamRead
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed separableUnary streamUnary separableStreamRead
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportReplay
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed replayUnary readbackUnary replayReadbackReal
  exact
    ⟨streamUnary, readbackUnary, metricReadUnary, completionReadUnary, denseReadUnary,
      realReadUnary, metricStreamRead, completeStreamRead, separableStreamRead,
      replayReadbackReal, provenancePkg, localNamePkg⟩

end BEDC.Derived.PolishspaceUp
