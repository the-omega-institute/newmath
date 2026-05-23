import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_modulus_ledger
    {Z S M R Q H C P N depthLock comparisonRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont S M depthLock ->
        Cont depthLock Q comparisonRead ->
          Cont comparisonRead N refusalRead ->
            UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory depthLock ∧
              UnaryHistory comparisonRead ∧ UnaryHistory refusalRead ∧ hsame H (append Z S) ∧
                Cont S M depthLock ∧ Cont depthLock Q comparisonRead ∧
                  Cont comparisonRead N refusalRead ∧ Cont M R Q ∧ Cont Q H C ∧
                    Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet depthRoute comparisonRoute refusalRoute
  obtain ⟨_unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, modulusRoute, continuationRoute,
    nameRoute⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unaryDepth : UnaryHistory depthLock :=
    unary_cont_closed unaryS unaryM depthRoute
  have unaryComparison : UnaryHistory comparisonRead :=
    unary_cont_closed unaryDepth unaryQ comparisonRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed _unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH continuationRoute
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC _unaryP nameRoute
  have unaryRefusal : UnaryHistory refusalRead :=
    unary_cont_closed unaryComparison unaryN refusalRoute
  exact
    ⟨unaryS, unaryM, unaryQ, unaryDepth, unaryComparison, unaryRefusal, sameH, depthRoute,
      comparisonRoute, refusalRoute, modulusRoute, continuationRoute, nameRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
