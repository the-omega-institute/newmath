import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_route_totality_certificate
    {Z S M R Q H C P N depthRead routeRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R depthRead ->
        Cont depthRead H routeRead ->
          Cont N Q refusalRead ->
            SemanticNameCert
                (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row routeRead ∧ Cont M R depthRead ∧
                    Cont depthRead H routeRead)
                (fun row : BHist => hsame row routeRead ∨ hsame row refusalRead)
                hsame ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory routeRead ∧
                UnaryHistory refusalRead ∧ Cont M R Q ∧ Cont M R depthRead ∧
                  Cont depthRead H routeRead ∧ Cont N Q refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet depthRoute routeRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC,
    _routeN⟩ := packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed depthUnary unaryH routeRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  have sourceAtRoute : hsame routeRead routeRead ∧ UnaryHistory routeRead :=
    ⟨hsame_refl routeRead, routeUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row routeRead ∧ Cont M R depthRead ∧ Cont depthRead H routeRead)
        (fun row : BHist => hsame row routeRead ∨ hsame row refusalRead)
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
      exact ⟨source.left, depthRoute, routeRoute⟩
    ledger_sound := by
      intro _row source
      exact Or.inl source.left
  }
  exact
    ⟨cert, routeClosure.left, unaryH, routeUnary, refusalUnary, routeQ, depthRoute,
      routeRoute, refusalRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
