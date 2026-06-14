import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_refusal_public_nonescape
    {Z S M R Q H C P N publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q publicRead ->
        SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row publicRead)
            (fun row : BHist => hsame row publicRead ∧ Cont N Q publicRead)
            hsame ∧
          UnaryHistory publicRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert
  intro packet publicRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ Cont N Q publicRead)
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicRoute⟩
  }
  exact ⟨cert, publicUnary, routeClosure.right.right.right⟩

end BEDC.Derived.CriticalLineWitnessUp
