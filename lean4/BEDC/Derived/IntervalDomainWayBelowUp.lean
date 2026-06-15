import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalDomainWayBelowUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def IntervalDomainWayBelowCarrier (O I M N S Q E H C P A : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory O ∧ UnaryHistory I ∧ UnaryHistory N ∧ UnaryHistory Q ∧
    UnaryHistory C ∧ hsame H (append O I) ∧ Cont O I M ∧ Cont M N S ∧
      Cont S Q E ∧ Cont E C P ∧ Cont P H A

theorem IntervalDomainWayBelowCarrier_namecert_obligations
    {O I M N S Q E H C P A : BHist} :
    IntervalDomainWayBelowCarrier O I M N S Q E H C P A ->
      UnaryHistory O ∧ UnaryHistory I ∧ UnaryHistory M ∧ UnaryHistory N ∧
        UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory P ∧
          UnaryHistory A ∧ hsame H (append O I) ∧ Cont O I M ∧ Cont M N S ∧
            Cont S Q E ∧ Cont E C P ∧ Cont P H A := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier
  obtain ⟨unaryO, unaryI, unaryN, unaryQ, unaryC, sameH, routeOIM, routeMNS,
    routeSQE, routeECP, routePHA⟩ := carrier
  have unaryM : UnaryHistory M := unary_cont_closed unaryO unaryI routeOIM
  have unaryS : UnaryHistory S := unary_cont_closed unaryM unaryN routeMNS
  have unaryE : UnaryHistory E := unary_cont_closed unaryS unaryQ routeSQE
  have unaryP : UnaryHistory P := unary_cont_closed unaryE unaryC routeECP
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryO unaryI rfl) (hsame_symm sameH)
  have unaryA : UnaryHistory A := unary_cont_closed unaryP unaryH routePHA
  exact
    ⟨unaryO, unaryI, unaryM, unaryN, unaryS, unaryQ, unaryE, unaryP, unaryA,
      sameH, routeOIM, routeMNS, routeSQE, routeECP, routePHA⟩

end BEDC.Derived.IntervalDomainWayBelowUp
