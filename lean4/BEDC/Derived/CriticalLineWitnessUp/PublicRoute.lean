import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessPublicRoute {Z S M R Q H C P N publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q publicRead ->
        SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row C ∨ hsame row N ∨
                hsame row publicRead)
            (fun row : BHist => hsame row publicRead ∧ Cont N Q publicRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory C ∧
            UnaryHistory N ∧ UnaryHistory publicRead ∧ hsame H (append Z S) ∧
              Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont N Q publicRead := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet publicRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row C ∨ hsame row N ∨
              hsame row publicRead)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, routeClosure.left, routeClosure.right.left,
      routeClosure.right.right.left, publicUnary, sameH, routeQ, routeC, routeN, publicRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
