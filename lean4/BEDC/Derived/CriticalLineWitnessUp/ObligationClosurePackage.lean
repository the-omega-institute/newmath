import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_obligation_closure_package
    {Z S M R Q H C P N zeroStripRead modulusRead refusalRead closureRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont zeroStripRead Q modulusRead ->
          Cont N Q refusalRead ->
            Cont refusalRead C closureRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                      hsame row Q ∨ hsame row closureRead)
                  (fun row : BHist =>
                    hsame row closureRead ∧ Cont refusalRead C closureRead)
                  hsame ∧
                UnaryHistory closureRead ∧ hsame H (append Z S) ∧
                  Cont Z S zeroStripRead ∧ Cont zeroStripRead Q modulusRead ∧
                    Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont N Q refusalRead ∧
                      Cont refusalRead C closureRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripRoute modulusRoute refusalRoute closureRoute
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
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have _modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed zeroStripUnary unaryQ modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed refusalUnary unaryC closureRoute
  have sourceAtClosure : hsame closureRead closureRead ∧ UnaryHistory closureRead :=
    ⟨hsame_refl closureRead, closureUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row closureRead)
          (fun row : BHist => hsame row closureRead ∧ Cont refusalRead C closureRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro closureRead sourceAtClosure
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, closureRoute⟩
  }
  exact
    ⟨cert, closureUnary, sameH, zeroStripRoute, modulusRoute, routeQ, routeC, routeN,
      refusalRoute, closureRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
