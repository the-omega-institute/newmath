import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_downstream_consumer_totality
    {Z S M R Q H C P N rootRead handoff classifierRead budgetRead lockedRead
      downstream : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q rootRead ->
        Cont rootRead C handoff ->
          Cont Z S classifierRead ->
            Cont classifierRead H budgetRead ->
              Cont budgetRead Q lockedRead ->
                Cont handoff lockedRead downstream ->
                  SemanticNameCert
                      (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row handoff ∨ hsame row lockedRead ∨
                          hsame row downstream ∨ hsame row N ∨ hsame row Q)
                      (fun row : BHist =>
                        hsame row downstream ∧ Cont handoff lockedRead downstream)
                      hsame ∧
                    UnaryHistory handoff ∧ UnaryHistory lockedRead ∧
                      UnaryHistory downstream ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet rootRoute handoffRoute classifierRoute budgetRoute lockedRoute downstreamRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed unaryAppend unaryQ rootRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed rootUnary unaryC handoffRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed unaryZ unaryS classifierRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed classifierUnary unaryH budgetRoute
  have lockedUnary : UnaryHistory lockedRead :=
    unary_cont_closed budgetUnary unaryQ lockedRoute
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed handoffUnary lockedUnary downstreamRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row lockedRead ∨ hsame row downstream ∨
              hsame row N ∨ hsame row Q)
          (fun row : BHist => hsame row downstream ∧ Cont handoff lockedRead downstream)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstream ⟨hsame_refl downstream, downstreamUnary⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, downstreamRoute⟩
  }
  exact ⟨cert, handoffUnary, lockedUnary, downstreamUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
