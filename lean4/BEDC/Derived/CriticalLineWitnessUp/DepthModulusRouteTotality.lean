import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_depth_modulus_route_totality
    {Z S M R Q H C P N depthRead modulusRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R depthRead ->
        Cont depthRead H modulusRead ->
          Cont N Q refusalRead ->
            SemanticNameCert
                (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row depthRead ∨ hsame row modulusRead ∨ hsame row refusalRead)
                (fun row : BHist => hsame row modulusRead ∧ Cont depthRead H modulusRead)
                hsame ∧
              UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧
                UnaryHistory N ∧ UnaryHistory depthRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory refusalRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                    Cont M R depthRead ∧ Cont depthRead H modulusRead ∧
                      Cont N Q refusalRead ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier depthRoute modulusRoute refusalRoute
  have carrierPacket := carrier
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    carrier
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure carrierPacket
  have unaryQ : UnaryHistory Q := routeClosure.left
  have unaryN : UnaryHistory N := routeClosure.right.right.left
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed depthUnary unaryH modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have sourceAtModulus : hsame modulusRead modulusRead ∧ UnaryHistory modulusRead :=
    ⟨hsame_refl modulusRead, modulusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row depthRead ∨ hsame row modulusRead ∨ hsame row refusalRead)
          (fun row : BHist => hsame row modulusRead ∧ Cont depthRead H modulusRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead sourceAtModulus
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, modulusRoute⟩
  }
  exact
    ⟨cert, unaryM, unaryR, unaryQ, unaryH, unaryN, depthUnary, modulusUnary,
      refusalUnary, sameH, routeQ, depthRoute, modulusRoute, refusalRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
