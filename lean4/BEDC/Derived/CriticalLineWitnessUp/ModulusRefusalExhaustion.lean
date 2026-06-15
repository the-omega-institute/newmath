import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessModulusRefusalExhaustion
    {Z S M R Q H C P N sourceRead modulusRead refusalRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R modulusRead ->
          Cont sourceRead modulusRead refusalRead ->
            Cont refusalRead N boundaryRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                      hsame row Q ∨ hsame row boundaryRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Z S sourceRead ∧
                      Cont M R modulusRead ∧ Cont sourceRead modulusRead refusalRead ∧
                        Cont refusalRead N boundaryRead ∧ hsame H (append Z S))
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory refusalRead ∧ UnaryHistory boundaryRead ∧
                    hsame H (append Z S) := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute refusalRoute boundaryRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed sourceUnary modulusUnary refusalRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed refusalUnary routeClosure.right.right.left boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S sourceRead ∧ Cont M R modulusRead ∧
              Cont sourceRead modulusRead refusalRead ∧ Cont refusalRead N boundaryRead ∧
                hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, modulusRoute, refusalRoute, boundaryRoute,
          sameH⟩
  }
  exact ⟨cert, sourceUnary, modulusUnary, refusalUnary, boundaryUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
