import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_refusal_source_exactness
    {Z S M R Q H C P N sourceRead lockedRead rhBoundary : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S sourceRead →
        Cont sourceRead Q lockedRead →
          Cont lockedRead N rhBoundary →
            SemanticNameCert
                (fun row : BHist => hsame row rhBoundary ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row sourceRead ∨ hsame row lockedRead ∨
                        hsame row rhBoundary)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z S sourceRead ∧ Cont sourceRead Q lockedRead ∧
                    Cont lockedRead N rhBoundary ∧ hsame H (append Z S))
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory sourceRead ∧
                UnaryHistory lockedRead ∧ UnaryHistory rhBoundary ∧ hsame H (append Z S) ∧
                  Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute lockedRoute rhRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC _unaryP routeN
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have lockedUnary : UnaryHistory lockedRead :=
    unary_cont_closed sourceUnary unaryQ lockedRoute
  have rhUnary : UnaryHistory rhBoundary :=
    unary_cont_closed lockedUnary unaryN rhRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row sourceRead ∨ hsame row lockedRead ∨
                  hsame row rhBoundary)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S sourceRead ∧ Cont sourceRead Q lockedRead ∧
              Cont lockedRead N rhBoundary ∧ hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhBoundary ⟨hsame_refl rhBoundary, rhUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, lockedRoute, rhRoute, sameH⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, sourceUnary, lockedUnary, rhUnary, sameH, routeQ,
      routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
