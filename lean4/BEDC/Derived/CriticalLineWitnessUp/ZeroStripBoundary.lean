import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessZeroStripBoundary
    {Z S M R Q H C P N zeroRead routeRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont zeroRead C routeRead ->
          SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Z ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row routeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont Z S zeroRead ∧ Cont zeroRead C routeRead)
              hsame ∧
            UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute route
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryZeroRead : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have unaryRouteRead : UnaryHistory routeRead :=
    unary_cont_closed unaryZeroRead routeClosure.right.left route
  have sourceAtRoute : hsame routeRead routeRead ∧ UnaryHistory routeRead :=
    ⟨hsame_refl routeRead, unaryRouteRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zeroRead ∧ Cont zeroRead C routeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead sourceAtRoute
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, zeroRoute, route⟩
  }
  exact ⟨cert, unaryRouteRead⟩

theorem CriticalLineWitnessCarrier_zero_strip_boundary {Z S M R Q H C P N zeroRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        SemanticNameCert
            (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row zeroRead ∧ Cont Z S zeroRead)
            (fun row : BHist => hsame row zeroRead ∧ hsame H (append Z S))
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory zeroRead ∧
            hsame H (append Z S) ∧ Cont Z S zeroRead ∧ Cont M R Q ∧ Cont Q H C ∧
              Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have sourceAtZero : hsame zeroRead zeroRead ∧ UnaryHistory zeroRead :=
    ⟨hsame_refl zeroRead, zeroUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row zeroRead ∧ Cont Z S zeroRead)
          (fun row : BHist => hsame row zeroRead ∧ hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zeroRead sourceAtZero
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
      exact ⟨source.left, zeroRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sameH⟩
  }
  exact ⟨cert, unaryZ, unaryS, zeroUnary, sameH, zeroRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
