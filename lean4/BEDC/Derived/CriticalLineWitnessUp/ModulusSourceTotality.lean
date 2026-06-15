import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_source_totality
    {Z S M R Q H C P N zeroRead modulusRead rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont zeroRead Q modulusRead ->
          Cont N Q rhRead ->
            SemanticNameCert
                (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
                    hsame row modulusRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z S zeroRead ∧ Cont zeroRead Q modulusRead ∧
                    Cont N Q rhRead)
                hsame ∧
              UnaryHistory zeroRead ∧ UnaryHistory modulusRead ∧ UnaryHistory rhRead ∧
                hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert UnaryHistory
  intro packet zeroRoute modulusRoute rhRoute
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
  have unaryZeroRead : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryZeroRead unaryQ modulusRoute
  have unaryRhRead : UnaryHistory rhRead :=
    unary_cont_closed unaryN unaryQ rhRoute
  have sourceAtModulus :
      (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row) modulusRead :=
    ⟨hsame_refl modulusRead, unaryModulusRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row modulusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zeroRead ∧ Cont zeroRead Q modulusRead ∧
              Cont N Q rhRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead sourceAtModulus
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
      exact ⟨source.right, zeroRoute, modulusRoute, rhRoute⟩
  }
  exact ⟨cert, unaryZeroRead, unaryModulusRead, unaryRhRead, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
