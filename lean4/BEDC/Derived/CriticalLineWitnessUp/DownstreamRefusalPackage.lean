import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_downstream_refusal_package
    {Z S M R Q H C P N refusalRead rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead C rhRead ->
          SemanticNameCert
              (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                  hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N ∨ hsame row refusalRead ∨ hsame row rhRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont N Q refusalRead ∧ Cont refusalRead C rhRead)
              hsame ∧
            UnaryHistory refusalRead ∧ UnaryHistory rhRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute rhRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unaryRefusal : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have unaryRh : UnaryHistory rhRead :=
    unary_cont_closed unaryRefusal unaryC rhRoute
  have sourceAtRh : hsame rhRead rhRead ∧ UnaryHistory rhRead :=
    ⟨hsame_refl rhRead, unaryRh⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row refusalRead ∨ hsame row rhRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont N Q refusalRead ∧ Cont refusalRead C rhRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhRead sourceAtRh
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, refusalRoute, rhRoute⟩
  }
  exact ⟨cert, unaryRefusal, unaryRh, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
