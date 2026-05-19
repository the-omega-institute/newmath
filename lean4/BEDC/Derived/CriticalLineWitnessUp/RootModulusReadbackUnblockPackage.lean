import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_modulus_readback_unblock_package
    {Z S M R Q H C P N zetaRead modulusRead refusalRead rootRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q modulusRead ->
          Cont N Q refusalRead ->
            Cont refusalRead C rootRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                  (fun row : BHist => hsame row rootRead ∧ Cont Z S zetaRead)
                  (fun row : BHist => hsame row rootRead ∧ Cont refusalRead C rootRead)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                  UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧
                    UnaryHistory zetaRead ∧ UnaryHistory modulusRead ∧
                      UnaryHistory refusalRead ∧ UnaryHistory rootRead ∧
                        hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                          Cont zetaRead Q modulusRead ∧ Cont N Q refusalRead ∧
                            Cont refusalRead C rootRead ∧ Cont M R Q ∧ Cont Q H C ∧
                              Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute modulusRoute refusalRoute rootRoute
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
  have unaryZetaRead : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryZetaRead unaryQ modulusRoute
  have unaryRefusalRead : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have unaryRootRead : UnaryHistory rootRead :=
    unary_cont_closed unaryRefusalRead unaryC rootRoute
  have sourceAtRoot : hsame rootRead rootRead ∧ UnaryHistory rootRead :=
    ⟨hsame_refl rootRead, unaryRootRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row rootRead ∧ Cont Z S zetaRead)
          (fun row : BHist => hsame row rootRead ∧ Cont refusalRead C rootRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead sourceAtRoot
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
      exact ⟨source.left, zetaRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, rootRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, unaryZetaRead,
      unaryModulusRead, unaryRefusalRead, unaryRootRead, sameH, zetaRoute, modulusRoute,
      refusalRoute, rootRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
