import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_finished_endpoint_handoff
    {Z S M R Q H C P N depthRead endpointRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R depthRead ->
        Cont depthRead H endpointRead ->
          SemanticNameCert
              (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨
                  hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row endpointRead)
              (fun row : BHist =>
                hsame row endpointRead ∧ Cont M R depthRead ∧
                  Cont depthRead H endpointRead)
              hsame ∧
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧
              UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory depthRead ∧
                UnaryHistory endpointRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N ∧ Cont M R depthRead ∧
                    Cont depthRead H endpointRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet depthRoute endpointRoute
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
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed depthUnary unaryH endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row endpointRead)
          (fun row : BHist =>
            hsame row endpointRead ∧ Cont M R depthRead ∧
              Cont depthRead H endpointRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead
        ⟨hsame_refl endpointRead, endpointUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, depthRoute, endpointRoute⟩
  }
  exact
    ⟨cert, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN, depthUnary, endpointUnary,
      sameH, routeQ, routeC, routeN, depthRoute, endpointRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
