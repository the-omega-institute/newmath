import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRootZeroStripExclusion
    {Z S M R Q H C P N zeroStripRead sourceRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont zeroStripRead H sourceRead ->
          Cont N Q refusalRead ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row zeroStripRead ∨ hsame row sourceRead ∨ hsame row refusalRead)
                (fun row : BHist => UnaryHistory row)
                (fun row : BHist =>
                  hsame H (append Z S) ∧
                    (hsame row zeroStripRead ∨ hsame row sourceRead ∨
                      hsame row refusalRead))
                hsame ∧
              UnaryHistory zeroStripRead ∧ UnaryHistory sourceRead ∧
                UnaryHistory refusalRead ∧ hsame H (append Z S) ∧
                  Cont Z S zeroStripRead ∧ Cont zeroStripRead H sourceRead ∧
                    Cont N Q refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripRoute sourceRoute refusalRoute
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
  have unaryZeroStripRead : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have unarySourceRead : UnaryHistory sourceRead :=
    unary_cont_closed unaryZeroStripRead unaryH sourceRoute
  have unaryRefusalRead : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have sourceAtZero :
      hsame zeroStripRead zeroStripRead ∨ hsame zeroStripRead sourceRead ∨
        hsame zeroStripRead refusalRead :=
    Or.inl (hsame_refl zeroStripRead)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row zeroStripRead ∨ hsame row sourceRead ∨ hsame row refusalRead)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist =>
            hsame H (append Z S) ∧
              (hsame row zeroStripRead ∨ hsame row sourceRead ∨ hsame row refusalRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zeroStripRead sourceAtZero
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
        intro row other sameRows source
        cases source with
        | inl sameZero =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameZero)
        | inr rest =>
            cases rest with
            | inl sameSource =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSource))
            | inr sameRefusal =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameRefusal))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameZero =>
          exact unary_transport unaryZeroStripRead (hsame_symm sameZero)
      | inr rest =>
          cases rest with
          | inl sameSource =>
              exact unary_transport unarySourceRead (hsame_symm sameSource)
          | inr sameRefusal =>
              exact unary_transport unaryRefusalRead (hsame_symm sameRefusal)
    ledger_sound := by
      intro _row source
      exact ⟨sameH, source⟩
  }
  exact
    ⟨cert, unaryZeroStripRead, unarySourceRead, unaryRefusalRead, sameH, zeroStripRoute,
      sourceRoute, refusalRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
