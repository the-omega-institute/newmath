import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_modulus_refusal
    {Z S M R Q H C P N stripRead modulusRead refusalRead refusedModulus : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead M modulusRead ->
          Cont N Q refusalRead ->
            Cont modulusRead refusalRead refusedModulus ->
              SemanticNameCert
                  (fun row : BHist => hsame row refusedModulus ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row refusedModulus ∧ Cont Z S stripRead ∧
                      Cont N Q refusalRead)
                  (fun row : BHist =>
                    hsame row refusedModulus ∧
                      Cont modulusRead refusalRead refusedModulus)
                  hsame ∧
                UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory refusalRead ∧ UnaryHistory refusedModulus ∧
                    hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute modulusRoute refusalRoute refusedRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed stripUnary unaryM modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  have refusedUnary : UnaryHistory refusedModulus :=
    unary_cont_closed modulusUnary refusalUnary refusedRoute
  have sourceAtRefused : hsame refusedModulus refusedModulus ∧ UnaryHistory refusedModulus :=
    ⟨hsame_refl refusedModulus, refusedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusedModulus ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row refusedModulus ∧ Cont Z S stripRead ∧ Cont N Q refusalRead)
          (fun row : BHist =>
            hsame row refusedModulus ∧ Cont modulusRead refusalRead refusedModulus)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusedModulus sourceAtRefused
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
      exact ⟨source.left, stripRoute, refusalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusedRoute⟩
  }
  exact
    ⟨cert, stripUnary, modulusUnary, refusalUnary, refusedUnary, sameH, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
