import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalDomainWayBelowUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem IntervalDomainWayBelowApproximationRoute {O I M N S Q E H C P A consumer : BHist} :
    IntervalDomainWayBelowCarrier O I M N S Q E H C P A ->
      Cont A Q consumer ->
        UnaryHistory O ∧ UnaryHistory I ∧ UnaryHistory M ∧ UnaryHistory N ∧
          UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory P ∧
            UnaryHistory A ∧ UnaryHistory consumer ∧ hsame H (append O I) ∧
              Cont O I M ∧ Cont M N S ∧ Cont S Q E ∧ Cont E C P ∧ Cont P H A ∧
                Cont A Q consumer := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier consumerRoute
  have obligations :
      UnaryHistory O ∧ UnaryHistory I ∧ UnaryHistory M ∧ UnaryHistory N ∧
        UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory P ∧
          UnaryHistory A ∧ hsame H (append O I) ∧ Cont O I M ∧ Cont M N S ∧
            Cont S Q E ∧ Cont E C P ∧ Cont P H A :=
    IntervalDomainWayBelowCarrier_namecert_obligations carrier
  obtain ⟨unaryO, unaryI, unaryM, unaryN, unaryS, unaryQ, unaryE, unaryP, unaryA,
    sameH, routeOIM, routeMNS, routeSQE, routeECP, routePHA⟩ := obligations
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed unaryA unaryQ consumerRoute
  exact
    ⟨unaryO, unaryI, unaryM, unaryN, unaryS, unaryQ, unaryE, unaryP, unaryA,
      consumerUnary, sameH, routeOIM, routeMNS, routeSQE, routeECP, routePHA,
      consumerRoute⟩

theorem IntervalDomainWayBelowCarrier_obligation_closure_package
    {O I M N S Q E H C P A consumer : BHist} :
    IntervalDomainWayBelowCarrier O I M N S Q E H C P A ->
      Cont A Q consumer ->
        SemanticNameCert
            (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row O ∨ hsame row I ∨ hsame row M ∨ hsame row N ∨
                hsame row S ∨ hsame row Q ∨ hsame row E ∨ hsame row consumer)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont O I M ∧ Cont M N S ∧ Cont S Q E ∧
                Cont E C P ∧ Cont P H A ∧ Cont A Q consumer)
            hsame ∧
          UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier consumerRoute
  have route :
      UnaryHistory O ∧ UnaryHistory I ∧ UnaryHistory M ∧ UnaryHistory N ∧
        UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory P ∧
          UnaryHistory A ∧ UnaryHistory consumer ∧ hsame H (append O I) ∧
            Cont O I M ∧ Cont M N S ∧ Cont S Q E ∧ Cont E C P ∧ Cont P H A ∧
              Cont A Q consumer :=
    IntervalDomainWayBelowApproximationRoute carrier consumerRoute
  obtain ⟨_unaryO, _unaryI, _unaryM, _unaryN, _unaryS, _unaryQ, _unaryE,
    _unaryP, _unaryA, consumerUnary, _sameH, routeOIM, routeMNS, routeSQE,
    routeECP, routePHA, routeAQC⟩ := route
  have sourceAtConsumer :
      hsame consumer consumer ∧ UnaryHistory consumer :=
    ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row I ∨ hsame row M ∨ hsame row N ∨
              hsame row S ∨ hsame row Q ∨ hsame row E ∨ hsame row consumer)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont O I M ∧ Cont M N S ∧ Cont S Q E ∧
              Cont E C P ∧ Cont P H A ∧ Cont A Q consumer)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer sourceAtConsumer
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeOIM, routeMNS, routeSQE, routeECP, routePHA, routeAQC⟩
  }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.IntervalDomainWayBelowUp
