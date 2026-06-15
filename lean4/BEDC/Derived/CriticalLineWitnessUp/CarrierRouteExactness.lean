import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_carrier_route_exactness {Z S M R Q H C P N routeRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) (append M R) routeRead ->
        SemanticNameCert
            (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row routeRead ∧ Cont (append Z S) (append M R) routeRead)
            (fun row : BHist =>
              hsame row routeRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
              UnaryHistory N ∧ UnaryHistory routeRead ∧ hsame H (append Z S) ∧
                Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert
  intro packet route
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
  have unaryRoute : UnaryHistory routeRead :=
    unary_cont_closed
      (unary_cont_closed unaryZ unaryS (cont_intro rfl))
      (unary_cont_closed unaryM unaryR (cont_intro rfl))
      route
  have sourceAtRoute : hsame routeRead routeRead ∧ UnaryHistory routeRead :=
    ⟨hsame_refl routeRead, unaryRoute⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row routeRead ∧ Cont (append Z S) (append M R) routeRead)
          (fun row : BHist =>
            hsame row routeRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧
              Cont C P N)
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
      exact ⟨source.left, route⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sameH, routeQ, routeC, routeN⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryP, unaryN,
      unaryRoute, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
