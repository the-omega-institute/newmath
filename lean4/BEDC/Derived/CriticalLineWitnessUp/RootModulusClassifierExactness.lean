import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_modulus_classifier_exactness
    {Z S M R Q H C P N comparison classifier : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R comparison ->
        Cont comparison H classifier ->
          SemanticNameCert
              (fun row : BHist => hsame row classifier /\ UnaryHistory row)
              (fun row : BHist => hsame row classifier /\ Cont M R comparison)
              (fun row : BHist => hsame row classifier /\ Cont comparison H classifier)
              hsame /\
            UnaryHistory M /\ UnaryHistory R /\ UnaryHistory Q /\ UnaryHistory H /\
              UnaryHistory comparison /\ UnaryHistory classifier /\ hsame comparison Q /\
                hsame H (append Z S) /\ Cont M R comparison /\
                  Cont comparison H classifier := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame UnaryHistory
  intro packet comparisonRoute classifierRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC,
    _routeN⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed comparisonUnary unaryH classifierRoute
  have sameComparison : hsame comparison Q :=
    cont_deterministic comparisonRoute routeQ
  have sourceAtClassifier :
      (fun row : BHist => hsame row classifier /\ UnaryHistory row) classifier := by
    exact ⟨hsame_refl classifier, classifierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifier /\ UnaryHistory row)
          (fun row : BHist => hsame row classifier /\ Cont M R comparison)
          (fun row : BHist => hsame row classifier /\ Cont comparison H classifier)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifier sourceAtClassifier
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
      exact ⟨source.left, comparisonRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, classifierRoute⟩
  }
  exact
    ⟨cert, unaryM, unaryR, unaryQ, unaryH, comparisonUnary, classifierUnary,
      sameComparison, sameH, comparisonRoute, classifierRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
