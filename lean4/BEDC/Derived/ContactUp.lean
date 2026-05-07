import BEDC.Derived.DiffFormUp
import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ContactUp

open BEDC.Derived.DiffFormUp
open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ContactUpFormRow_obligation {degree probe tensor scalar antisym ledger contactForm
    derivative wedgeTop : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          UnaryHistory contactForm -> Cont scalar contactForm derivative ->
            Cont derivative antisym wedgeTop ->
              UnaryHistory tensor ∧ UnaryHistory scalar ∧ UnaryHistory derivative ∧
                UnaryHistory wedgeTop ∧ Cont scalar contactForm derivative ∧
                  Cont derivative antisym wedgeTop := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute contactUnary
  intro derivativeRoute wedgeRoute
  have diffRows :=
    DiffFormBHistLedger_exactness_obligation degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have tensorUnary : UnaryHistory tensor := diffRows.left
  have scalarUnary : UnaryHistory scalar := diffRows.right.left
  have derivativeUnary : UnaryHistory derivative :=
    unary_cont_closed scalarUnary contactUnary derivativeRoute
  have wedgeTopUnary : UnaryHistory wedgeTop :=
    unary_cont_closed derivativeUnary antisymUnary wedgeRoute
  exact And.intro tensorUnary
    (And.intro scalarUnary
      (And.intro derivativeUnary
        (And.intro wedgeTopUnary (And.intro derivativeRoute wedgeRoute))))

end BEDC.Derived.ContactUp
