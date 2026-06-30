import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_visible_modulus_consumer_totality
    {Z S M R Q H C P N modulusRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M Q modulusRead ->
        Cont H C refusalRead ->
          SemanticNameCert
              (fun row : BHist => hsame row modulusRead ∨ hsame row refusalRead)
              (fun row : BHist =>
                hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                  hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N ∨ hsame row modulusRead ∨ hsame row refusalRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont M Q modulusRead ∧ Cont H C refusalRead)
              hsame ∧
            UnaryHistory modulusRead ∧ UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet modulusRoute refusalRoute
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
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryQ modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryH unaryC refusalRoute
  have sourceAtModulus :
      (fun row : BHist => hsame row modulusRead ∨ hsame row refusalRead) modulusRead :=
    Or.inl (hsame_refl modulusRead)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∨ hsame row refusalRead)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row modulusRead ∨ hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q modulusRead ∧ Cont H C refusalRead)
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
        cases source with
        | inl sameModulus =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameModulus)
        | inr sameRefusal =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameRefusal)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameModulus =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl sameModulus)))))))))
      | inr sameRefusal =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr sameRefusal)))))))))
    ledger_sound := by
      intro row source
      cases source with
      | inl sameModulus =>
          exact ⟨unary_transport modulusUnary (hsame_symm sameModulus), modulusRoute, refusalRoute⟩
      | inr sameRefusal =>
          exact ⟨unary_transport refusalUnary (hsame_symm sameRefusal), modulusRoute, refusalRoute⟩
  }
  exact ⟨cert, modulusUnary, refusalUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
