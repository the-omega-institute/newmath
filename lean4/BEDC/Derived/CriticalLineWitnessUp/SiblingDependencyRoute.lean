import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessSiblingDependencyRoute
    {Z S M R Q H C P N zetaSource zeroLocus continuationBoundary witnessRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zetaSource →
        Cont zetaSource Q zeroLocus →
          Cont zeroLocus H continuationBoundary →
            Cont continuationBoundary N witnessRead →
              UnaryHistory zetaSource ∧ UnaryHistory zeroLocus ∧
                UnaryHistory continuationBoundary ∧ UnaryHistory witnessRead ∧
                  hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet zetaRoute zeroRoute continuationRoute witnessRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZetaSource : UnaryHistory zetaSource :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryZeroLocus : UnaryHistory zeroLocus :=
    unary_cont_closed unaryZetaSource unaryQ zeroRoute
  have unaryRoot : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryRoot (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unaryContinuationBoundary : UnaryHistory continuationBoundary :=
    unary_cont_closed unaryZeroLocus unaryH continuationRoute
  have unaryWitnessRead : UnaryHistory witnessRead :=
    unary_cont_closed unaryContinuationBoundary unaryN witnessRoute
  exact
    ⟨unaryZetaSource, unaryZeroLocus, unaryContinuationBoundary, unaryWitnessRead, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
