import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_transport_replay_obligation
    {Z S M R Q H C P N replay : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont H C replay →
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory replay ∧ hsame H (append Z S) ∧
          Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont H C replay := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet replayRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryReplay : UnaryHistory replay :=
    unary_cont_closed unaryH routeClosure.right.left replayRoute
  exact
    ⟨unaryH, routeClosure.right.left, unaryReplay, routeClosure.right.right.right, routeQ,
      routeC, routeN, replayRoute⟩

theorem CriticalLineWitnessHsameContLedgerObligation
    {Z S M R Q H C P N replayRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont H C replayRead →
        SemanticNameCert
            (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row replayRead)
            (fun row : BHist =>
              hsame row replayRead ∧ Cont H C replayRead ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N)
            hsame ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory replayRead ∧
            hsame H (append Z S) ∧ Cont H C replayRead ∧ Cont M R Q ∧ Cont Q H C ∧
              Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet replayRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryReplay : UnaryHistory replayRead :=
    unary_cont_closed unaryH routeClosure.right.left replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row replayRead)
          (fun row : BHist =>
            hsame row replayRead ∧ Cont H C replayRead ∧ Cont M R Q ∧
              Cont Q H C ∧ Cont C P N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, unaryReplay⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, replayRoute, routeQ, routeC, routeN⟩
  }
  exact
    ⟨cert, unaryH, routeClosure.right.left, unaryReplay, routeClosure.right.right.right,
      replayRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
