import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_classifier_exactness
    {Z S M R Q H C P N classifierRead namedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont H C classifierRead ->
        Cont classifierRead P namedRead ->
          SemanticNameCert
              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row namedRead ∧ Cont H C classifierRead)
              (fun row : BHist => hsame row namedRead ∧ Cont classifierRead P namedRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
              UnaryHistory classifierRead ∧ UnaryHistory namedRead ∧
                hsame H (append Z S) ∧ Cont H C classifierRead ∧
                  Cont classifierRead P namedRead ∧ Cont M R Q ∧ Cont Q H C ∧
                    Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet classifierRoute namedRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed unaryH unaryC classifierRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed classifierUnary unaryP namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row namedRead ∧ Cont H C classifierRead)
          (fun row : BHist => hsame row namedRead ∧ Cont classifierRead P namedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact ⟨source.left, classifierRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namedRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryH, unaryC, classifierUnary, namedUnary, sameH,
      classifierRoute, namedRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
