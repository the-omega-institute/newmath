import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_consumer_threshold
    {Z S M R Q H C P N thresholdRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q C thresholdRead ->
        SemanticNameCert
            (fun row : BHist => hsame row thresholdRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row M ∨ hsame row Q ∨ hsame row thresholdRead)
            (fun row : BHist => UnaryHistory row ∧ Cont Q C thresholdRead)
            hsame ∧
          UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory thresholdRead ∧
            hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q C thresholdRead ∧
              Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet thresholdRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryQ unaryC thresholdRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row thresholdRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row M ∨ hsame row Q ∨ hsame row thresholdRead)
          (fun row : BHist => UnaryHistory row ∧ Cont Q C thresholdRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro thresholdRead
        ⟨hsame_refl thresholdRead, thresholdUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, thresholdRoute⟩
  }
  exact
    ⟨cert, unaryM, unaryQ, thresholdUnary, sameH, routeQ, thresholdRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
