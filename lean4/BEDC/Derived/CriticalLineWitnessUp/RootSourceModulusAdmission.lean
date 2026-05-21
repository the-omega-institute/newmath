import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_source_modulus_admission
    {Z S M R Q H C P N sourceRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R modulusRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧
              hsame H (append Z S) ∧ Cont Z S sourceRead ∧ Cont M R modulusRead ∧
                Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sourceRoute modulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unarySourceRead : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unarySourceRead, unaryModulusRead,
      sameH, sourceRoute, modulusRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
