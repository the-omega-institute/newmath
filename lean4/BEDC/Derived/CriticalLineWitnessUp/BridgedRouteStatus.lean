import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_bridged_route_status
    {Z S M R Q H C P N bridgeRead refusalRead statusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q bridgeRead ->
        Cont N Q refusalRead ->
          Cont bridgeRead refusalRead statusRead ->
            SemanticNameCert
                (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row bridgeRead ∨ hsame row refusalRead ∨ hsame row statusRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont (append Z S) Q bridgeRead ∧
                    Cont N Q refusalRead ∧ Cont bridgeRead refusalRead statusRead)
                hsame ∧
              UnaryHistory statusRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet bridgeRoute refusalRoute statusRoute
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
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed sourceUnary unaryQ bridgeRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have statusUnary : UnaryHistory statusRead :=
    unary_cont_closed bridgeUnary refusalUnary statusRoute
  have sourceAtStatus : hsame statusRead statusRead ∧ UnaryHistory statusRead :=
    ⟨hsame_refl statusRead, statusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bridgeRead ∨ hsame row refusalRead ∨ hsame row statusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont (append Z S) Q bridgeRead ∧ Cont N Q refusalRead ∧
              Cont bridgeRead refusalRead statusRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro statusRead sourceAtStatus
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
      intro row source
      right
      right
      exact source.left
    ledger_sound := by
      intro row source
      exact ⟨source.right, bridgeRoute, refusalRoute, statusRoute⟩
  }
  exact ⟨cert, statusUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
