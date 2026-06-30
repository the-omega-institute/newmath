import BEDC.Derived.WronskianUp.LinearDependenceWitness

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WronskianCarrier_differential_equation_consumer_handoff [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N determinantRead valueRead sealRead witnessRead publicRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WronskianObligationRowSpec F D J Omega S R E H C P N F →
      WronskianObligationRowSpec F D J Omega S R E H C P N D →
        WronskianObligationRowSpec F D J Omega S R E H C P N J →
          WronskianObligationRowSpec F D J Omega S R E H C P N Omega →
            WronskianObligationRowSpec F D J Omega S R E H C P N E →
              UnaryHistory F →
                UnaryHistory D →
                  UnaryHistory J →
                    UnaryHistory Omega →
                      UnaryHistory S →
                        UnaryHistory R →
                          UnaryHistory E →
                            UnaryHistory H →
                              UnaryHistory consumerRead →
                                Cont F D J →
                                  Cont J Omega determinantRead →
                                    Cont S R valueRead →
                                      Cont valueRead E sealRead →
                                        Cont determinantRead sealRead witnessRead →
                                          Cont sealRead H publicRead →
                                            Cont publicRead consumerRead consumerRead →
                                              PkgSig bundle witnessRead pkg →
                                                PkgSig bundle publicRead pkg →
                                                  UnaryHistory determinantRead ∧
                                                    UnaryHistory valueRead ∧
                                                      UnaryHistory sealRead ∧
                                                        UnaryHistory witnessRead ∧
                                                          UnaryHistory publicRead ∧
                                                            WronskianObligationRowSpec F D J
                                                              Omega S R E H C P N E ∧
                                                              Cont determinantRead sealRead
                                                                witnessRead ∧
                                                                PkgSig bundle witnessRead
                                                                  pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame UnaryHistory
  intro _fSpec _dSpec jSpec omegaSpec eSpec fUnary _dUnary jUnary omegaUnary sUnary
    rUnary eUnary hUnary _consumerUnary familyRoute determinantRoute valueRoute sealRoute
    witnessRoute publicRoute _consumerRoute witnessPkg _publicPkg
  have determinantUnary : UnaryHistory determinantRead :=
    unary_cont_closed jUnary omegaUnary determinantRoute
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed sUnary rUnary valueRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed valueUnary eUnary sealRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed determinantUnary sealUnary witnessRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary hUnary publicRoute
  exact
    ⟨determinantUnary, valueUnary, sealUnary, witnessUnary, publicUnary, eSpec,
      witnessRoute, witnessPkg⟩

end BEDC.Derived.WronskianUp
