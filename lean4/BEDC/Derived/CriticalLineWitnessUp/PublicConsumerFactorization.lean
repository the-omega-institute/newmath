import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_public_consumer_factorization
    {Z S M R Q H C P N stripRead modulusRead publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q modulusRead ->
          Cont modulusRead N publicRead ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row N ∨ Cont modulusRead N publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z S stripRead ∧
                    Cont stripRead Q modulusRead ∧ Cont modulusRead N publicRead)
                hsame ∧ UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧
              UnaryHistory publicRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute modulusRoute publicRoute
  obtain ⟨unaryQ, _unaryC, unaryN, sameH⟩ :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, _routeQ, _routeC,
    _routeN⟩ := packet
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed stripUnary unaryQ modulusRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed modulusUnary unaryN publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row N ∨ Cont modulusRead N publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S stripRead ∧ Cont stripRead Q modulusRead ∧
              Cont modulusRead N publicRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr publicRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, stripRoute, modulusRoute, publicRoute⟩
  }
  exact ⟨cert, stripUnary, modulusUnary, publicUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
