import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessZetaRhDependencyCertificate
    {Z S M R Q H C P N zetaSource zeroSurface rhBoundary witnessRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaSource ->
        Cont zetaSource Q zeroSurface ->
          Cont zeroSurface H rhBoundary ->
            Cont rhBoundary N witnessRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row zetaSource ∨ hsame row zeroSurface ∨ hsame row rhBoundary ∨
                      hsame row witnessRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Z S zetaSource ∧ Cont zetaSource Q zeroSurface ∧
                      Cont zeroSurface H rhBoundary ∧ Cont rhBoundary N witnessRead)
                  hsame ∧
                UnaryHistory zetaSource ∧ UnaryHistory zeroSurface ∧ UnaryHistory rhBoundary ∧
                  UnaryHistory witnessRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute zeroRoute rhRoute witnessRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZetaSource : UnaryHistory zetaSource :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryZeroSurface : UnaryHistory zeroSurface :=
    unary_cont_closed unaryZetaSource unaryQ zeroRoute
  have unaryRoot : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryRoot (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unaryRhBoundary : UnaryHistory rhBoundary :=
    unary_cont_closed unaryZeroSurface unaryH rhRoute
  have unaryWitnessRead : UnaryHistory witnessRead :=
    unary_cont_closed unaryRhBoundary unaryN witnessRoute
  have sourceAtWitness :
      (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row) witnessRead := by
    exact ⟨hsame_refl witnessRead, unaryWitnessRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zetaSource ∨ hsame row zeroSurface ∨ hsame row rhBoundary ∨
              hsame row witnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zetaSource ∧ Cont zetaSource Q zeroSurface ∧
              Cont zeroSurface H rhBoundary ∧ Cont rhBoundary N witnessRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro witnessRead sourceAtWitness
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, zetaRoute, zeroRoute, rhRoute, witnessRoute⟩
  }
  exact
    ⟨cert, unaryZetaSource, unaryZeroSurface, unaryRhBoundary, unaryWitnessRead, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
