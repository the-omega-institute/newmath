import BEDC.Derived.LocatedUniformCompletionUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.LocatedUniformCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedUniformCompletionCarrier_density_route [AskSetup] [PackageSetup]
    {F U B S R E H C P N completionRead regularRead windowRead readbackRead sealRead
      transportRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F →
      UnaryHistory U →
        UnaryHistory B →
          UnaryHistory S →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory C →
                    Cont F U completionRead →
                      Cont completionRead B regularRead →
                        Cont regularRead S windowRead →
                          Cont windowRead R readbackRead →
                            Cont readbackRead E sealRead →
                              Cont sealRead H transportRead →
                                Cont transportRead C replayRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      UnaryHistory completionRead ∧
                                        UnaryHistory regularRead ∧ UnaryHistory windowRead ∧
                                          UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                                            UnaryHistory transportRead ∧
                                              UnaryHistory replayRead ∧
                                                Cont F U completionRead ∧
                                                  Cont completionRead B regularRead ∧
                                                    Cont regularRead S windowRead ∧
                                                      Cont windowRead R readbackRead ∧
                                                        Cont readbackRead E sealRead ∧
                                                          Cont sealRead H transportRead ∧
                                                            Cont transportRead C replayRead ∧
                                                              PkgSig bundle P pkg ∧
                                                                PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro fUnary uUnary bUnary sUnary rUnary eUnary hUnary cUnary completionRoute
    regularRoute windowRoute readbackRoute sealRoute transportRoute replayRoute provenancePkg
    namePkg
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed fUnary uUnary completionRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed completionUnary bUnary regularRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed regularUnary sUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed sealUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  exact
    ⟨completionUnary, regularUnary, windowUnary, readbackUnary, sealUnary, transportUnary,
      replayUnary, completionRoute, regularRoute, windowRoute, readbackRoute, sealRoute,
      transportRoute, replayRoute, provenancePkg, namePkg⟩

end BEDC.Derived.LocatedUniformCompletionUp
