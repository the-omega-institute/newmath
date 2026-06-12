import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRootZeroStripModulusTotality
    {Z S M R Q H C P N zeroStripRead modulusRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont zeroStripRead Q modulusRead ->
          Cont N Q refusalRead ->
            SemanticNameCert
                (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row modulusRead)
                (fun row : BHist => hsame row modulusRead ∧ Cont zeroStripRead Q modulusRead)
                hsame ∧
              SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row refusalRead)
                (fun row : BHist => hsame row refusalRead ∧ Cont N Q refusalRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory zeroStripRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory refusalRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                    Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripRoute modulusRoute refusalRoute
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
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryZeroStripRead unaryQ modulusRoute
  have unaryRefusalRead : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have modulusCert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row modulusRead)
          (fun row : BHist => hsame row modulusRead ∧ Cont zeroStripRead Q modulusRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro modulusRead ⟨hsame_refl modulusRead, unaryModulusRead⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, modulusRoute⟩
  }
  have refusalCert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row refusalRead)
          (fun row : BHist => hsame row refusalRead ∧ Cont N Q refusalRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refusalRead ⟨hsame_refl refusalRead, unaryRefusalRead⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute⟩
  }
  exact
    ⟨modulusCert, refusalCert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryZeroStripRead,
      unaryModulusRead, unaryRefusalRead, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
