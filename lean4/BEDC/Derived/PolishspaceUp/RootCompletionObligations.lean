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

theorem PolishspaceRootCompletionObligations [AskSetup] [PackageSetup]
    {metric complete stream readback ledger transport route completionRead observationRead
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric ->
      UnaryHistory complete ->
        UnaryHistory stream ->
          UnaryHistory readback ->
            UnaryHistory ledger ->
              UnaryHistory transport ->
                Cont complete stream completionRead ->
                  Cont ledger transport route ->
                    Cont route readback observationRead ->
                      PkgSig bundle provenance pkg ->
                        PkgSig bundle localName pkg ->
                          UnaryHistory complete ∧ UnaryHistory stream ∧
                            UnaryHistory completionRead ∧ UnaryHistory observationRead ∧
                              Cont complete stream completionRead ∧
                                Cont ledger transport route ∧
                                  Cont route readback observationRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle PkgSig
  intro _metricUnary completeUnary streamUnary readbackUnary ledgerUnary transportUnary
    completeStreamCompletion ledgerTransportRoute routeReadbackObservation provenancePkg
    localNamePkg
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed completeUnary streamUnary completeStreamCompletion
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportRoute
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed routeUnary readbackUnary routeReadbackObservation
  exact
    ⟨completeUnary, streamUnary, completionUnary, observationUnary, completeStreamCompletion,
      ledgerTransportRoute, routeReadbackObservation, provenancePkg, localNamePkg⟩

end BEDC.Derived.PolishspaceUp
