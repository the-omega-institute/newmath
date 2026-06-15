import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_refusal_ledger_exactness
    {Z S M R Q H C P N refusalRead gammaRead zetaRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead C gammaRead ->
          Cont refusalRead H zetaRead ->
            SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row refusalRead ∧ Cont N Q refusalRead)
                (fun row : BHist =>
                  hsame row refusalRead ∧ Cont refusalRead C gammaRead ∧
                    Cont refusalRead H zetaRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
                  UnaryHistory refusalRead ∧ UnaryHistory gammaRead ∧ UnaryHistory zetaRead ∧
                    hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                      Cont N Q refusalRead ∧ Cont refusalRead C gammaRead ∧
                        Cont refusalRead H zetaRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute gammaRoute zetaRoute
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
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have gammaUnary : UnaryHistory gammaRead :=
    unary_cont_closed refusalUnary unaryC gammaRoute
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed refusalUnary unaryH zetaRoute
  have sourceAtRefusal : hsame refusalRead refusalRead ∧ UnaryHistory refusalRead :=
    ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row refusalRead ∧ Cont N Q refusalRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont refusalRead C gammaRead ∧ Cont refusalRead H zetaRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceAtRefusal
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
      exact ⟨source.left, refusalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, gammaRoute, zetaRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN, refusalUnary,
      gammaUnary, zetaUnary, sameH, routeQ, routeC, routeN, refusalRoute, gammaRoute,
      zetaRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
