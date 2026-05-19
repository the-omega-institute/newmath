import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_gap_refusal_completeness
    {Z S M R Q H C P N zetaRead refusalRead gapRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zetaRead →
        Cont N Q refusalRead →
          Cont refusalRead H gapRead →
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
              UnaryHistory N ∧ UnaryHistory zetaRead ∧ UnaryHistory refusalRead ∧
                UnaryHistory gapRead ∧ hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                  Cont N Q refusalRead ∧ Cont refusalRead H gapRead ∧ Cont M R Q ∧
                    Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet zetaRoute refusalRoute gapRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryZetaRead : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryRefusalRead : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  have unaryGapRead : UnaryHistory gapRead :=
    unary_cont_closed unaryRefusalRead unaryH gapRoute
  exact
    ⟨unaryZ, unaryS, routeClosure.left, unaryH, routeClosure.right.right.left,
      unaryZetaRead, unaryRefusalRead, unaryGapRead, routeClosure.right.right.right,
      zetaRoute, refusalRoute, gapRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
