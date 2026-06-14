import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_rh_boundary_public_nonescape
    {Z S M R Q H C P N stripRead modulusRead refusalRead boundaryRead publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q modulusRead ->
          Cont N Q refusalRead ->
            Cont modulusRead refusalRead boundaryRead ->
              Cont boundaryRead C publicRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row N ∨
                        hsame row boundaryRead ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont Z S stripRead ∧
                        Cont stripRead Q modulusRead ∧ Cont N Q refusalRead ∧
                          Cont modulusRead refusalRead boundaryRead ∧
                            Cont boundaryRead C publicRead)
                    hsame ∧
                  UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧
                    UnaryHistory refusalRead ∧ UnaryHistory boundaryRead ∧
                      UnaryHistory publicRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory append
  intro packet stripRoute modulusRoute refusalRoute boundaryRoute publicRoute
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
  have unaryStrip : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have unaryModulus : UnaryHistory modulusRead :=
    unary_cont_closed unaryStrip unaryQ modulusRoute
  have unaryRefusal : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have unaryBoundary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryModulus unaryRefusal boundaryRoute
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unaryBoundary unaryC publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row N ∨
              hsame row boundaryRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S stripRead ∧ Cont stripRead Q modulusRead ∧
              Cont N Q refusalRead ∧ Cont modulusRead refusalRead boundaryRead ∧
                Cont boundaryRead C publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, unaryPublic⟩
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
      exact
        ⟨source.right, stripRoute, modulusRoute, refusalRoute, boundaryRoute, publicRoute⟩
  }
  exact
    ⟨cert, unaryStrip, unaryModulus, unaryRefusal, unaryBoundary, unaryPublic, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
