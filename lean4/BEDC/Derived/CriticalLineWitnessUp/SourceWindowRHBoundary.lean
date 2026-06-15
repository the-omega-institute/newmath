import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_window_rh_boundary
    {Z S M R Q H C P N sourceRead zeroBoundary rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead H zeroBoundary ->
          Cont zeroBoundary Q rhRead ->
            SemanticNameCert
                (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row H ∨ hsame row Q ∨
                    hsame row rhRead)
                (fun row : BHist =>
                  hsame row rhRead ∧ Cont Z S sourceRead ∧
                    Cont sourceRead H zeroBoundary ∧ Cont zeroBoundary Q rhRead)
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory zeroBoundary ∧ UnaryHistory rhRead ∧
                hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute zeroRoute rhRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unarySourceRead : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have unaryZeroBoundary : UnaryHistory zeroBoundary :=
    unary_cont_closed unarySourceRead unaryH zeroRoute
  have unaryRHRead : UnaryHistory rhRead :=
    unary_cont_closed unaryZeroBoundary unaryQ rhRoute
  have sourceAtRH :
      (fun row : BHist => hsame row rhRead ∧ UnaryHistory row) rhRead := by
    exact ⟨hsame_refl rhRead, unaryRHRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row H ∨ hsame row Q ∨
              hsame row rhRead)
          (fun row : BHist =>
            hsame row rhRead ∧ Cont Z S sourceRead ∧ Cont sourceRead H zeroBoundary ∧
              Cont zeroBoundary Q rhRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhRead sourceAtRH
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sourceRoute, zeroRoute, rhRoute⟩
  }
  exact
    ⟨cert, unarySourceRead, unaryZeroBoundary, unaryRHRead, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
