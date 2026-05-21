import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_public_readiness
    {Z S M R Q H C P N publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N (append Z S) publicRead ->
        SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row publicRead ∧ hsame H (append Z S))
            (fun row : BHist =>
              hsame row publicRead ∧ Cont N (append Z S) publicRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
            UnaryHistory publicRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
              Cont Q H C ∧ Cont C P N ∧ Cont N (append Z S) publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet publicRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have appendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport appendUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed unaryN appendUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row publicRead ∧ hsame H (append Z S))
          (fun row : BHist => hsame row publicRead ∧ Cont N (append Z S) publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact ⟨source.left, sameH⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryN, publicUnary, sameH, routeQ, routeC,
      routeN, publicRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
