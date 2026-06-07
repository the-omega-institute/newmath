import BEDC.Derived.AxiomPurityGateUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AxiomPurityGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomPurityGateWitnessPreservingConsumer [AskSetup] [PackageSetup]
    {T D F R L N reportRead refusalRead replacementRead auditRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory D →
        UnaryHistory F →
          UnaryHistory R →
            UnaryHistory L →
              UnaryHistory N →
                Cont T D reportRead →
                  Cont D F refusalRead →
                    Cont R L replacementRead →
                      Cont reportRead refusalRead auditRead →
                        Cont auditRead N consumerRead →
                          PkgSig bundle reportRead pkg →
                            PkgSig bundle auditRead pkg →
                              PkgSig bundle consumerRead pkg →
                                UnaryHistory reportRead ∧
                                  UnaryHistory refusalRead ∧
                                    UnaryHistory replacementRead ∧
                                      UnaryHistory auditRead ∧
                                        UnaryHistory consumerRead ∧
                                          Cont T D reportRead ∧
                                            Cont D F refusalRead ∧
                                              Cont R L replacementRead ∧
                                                Cont reportRead refusalRead auditRead ∧
                                                  Cont auditRead N consumerRead ∧
                                                    PkgSig bundle reportRead pkg ∧
                                                      PkgSig bundle auditRead pkg ∧
                                                        PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro tUnary dUnary fUnary rUnary lUnary nUnary reportRoute refusalRoute replacementRoute
    auditRoute consumerRoute reportPkg auditPkg consumerPkg
  have reportUnary : UnaryHistory reportRead :=
    unary_cont_closed tUnary dUnary reportRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed dUnary fUnary refusalRoute
  have replacementUnary : UnaryHistory replacementRead :=
    unary_cont_closed rUnary lUnary replacementRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed reportUnary refusalUnary auditRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed auditUnary nUnary consumerRoute
  exact
    ⟨reportUnary, refusalUnary, replacementUnary, auditUnary, consumerUnary, reportRoute,
      refusalRoute, replacementRoute, auditRoute, consumerRoute, reportPkg, auditPkg,
      consumerPkg⟩

end BEDC.Derived.AxiomPurityGateUp
