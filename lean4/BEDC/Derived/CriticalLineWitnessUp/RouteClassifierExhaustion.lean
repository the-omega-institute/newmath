import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRouteClassifierExhaustion
    {Z S M R Q H C P N classifierRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q H classifierRead ->
        hsame classifierRead C ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory classifierRead ∧
              hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H classifierRead ∧
                Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier qHClassifier _sameClassifier
  obtain ⟨zUnary, sUnary, mUnary, rUnary, _pUnary, sameH, mRQ, _qHC, cPN⟩ := carrier
  have qUnary : UnaryHistory Q :=
    unary_cont_closed mUnary rUnary mRQ
  have hUnary : UnaryHistory H :=
    unary_transport (unary_cont_closed zUnary sUnary (cont_intro rfl)) (hsame_symm sameH)
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed qUnary hUnary qHClassifier
  exact
    ⟨zUnary, sUnary, mUnary, rUnary, qUnary, hUnary, classifierUnary, sameH, mRQ,
      qHClassifier, cPN⟩

end BEDC.Derived.CriticalLineWitnessUp
