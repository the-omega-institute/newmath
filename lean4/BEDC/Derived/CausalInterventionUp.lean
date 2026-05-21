import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CausalInterventionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CausalIntervention_falsifiable_nonescape [AskSetup] [PackageSetup]
    {M S T D J R K _H _C _P N dependencyRead interventionRead rateRead commitmentRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory S →
        UnaryHistory D →
          UnaryHistory J →
            UnaryHistory R →
              UnaryHistory K →
                UnaryHistory N →
                  Cont M S T →
                    Cont T D dependencyRead →
                      Cont dependencyRead J interventionRead →
                        Cont interventionRead R rateRead →
                          Cont rateRead K commitmentRead →
                            Cont commitmentRead N publicRead →
                              PkgSig bundle publicRead pkg →
                                UnaryHistory T ∧ UnaryHistory dependencyRead ∧
                                  UnaryHistory interventionRead ∧ UnaryHistory rateRead ∧
                                    UnaryHistory commitmentRead ∧ UnaryHistory publicRead ∧
                                      Cont M S T ∧ Cont T D dependencyRead ∧
                                        Cont dependencyRead J interventionRead ∧
                                          Cont interventionRead R rateRead ∧
                                            Cont rateRead K commitmentRead ∧
                                              Cont commitmentRead N publicRead ∧
                                                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro unaryM unaryS unaryD unaryJ unaryR unaryK unaryN routeTarget routeDependency
    routeIntervention routeRate routeCommitment routePublic pkgSig
  have unaryT : UnaryHistory T :=
    unary_cont_closed unaryM unaryS routeTarget
  have unaryDependency : UnaryHistory dependencyRead :=
    unary_cont_closed unaryT unaryD routeDependency
  have unaryIntervention : UnaryHistory interventionRead :=
    unary_cont_closed unaryDependency unaryJ routeIntervention
  have unaryRate : UnaryHistory rateRead :=
    unary_cont_closed unaryIntervention unaryR routeRate
  have unaryCommitment : UnaryHistory commitmentRead :=
    unary_cont_closed unaryRate unaryK routeCommitment
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unaryCommitment unaryN routePublic
  exact
    ⟨unaryT, unaryDependency, unaryIntervention, unaryRate, unaryCommitment, unaryPublic,
      routeTarget, routeDependency, routeIntervention, routeRate, routeCommitment, routePublic,
      pkgSig⟩

end BEDC.Derived.CausalInterventionUp
