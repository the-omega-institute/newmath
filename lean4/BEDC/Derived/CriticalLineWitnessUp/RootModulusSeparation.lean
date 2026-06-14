import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_modulus_separation
    {Z S M R Q H C P N modulusRead classifierRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q modulusRead ->
        Cont M R classifierRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory modulusRead ∧
              UnaryHistory classifierRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                Cont (append Z S) Q modulusRead ∧ Cont M R classifierRead ∧
                  Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet modulusRoute classifierRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed (unary_cont_closed unaryZ unaryS (cont_intro rfl)) unaryQ modulusRoute
  have unaryClassifierRead : UnaryHistory classifierRead :=
    unary_cont_closed unaryM unaryR classifierRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryModulusRead,
      unaryClassifierRead, sameH, routeQ, modulusRoute, classifierRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
