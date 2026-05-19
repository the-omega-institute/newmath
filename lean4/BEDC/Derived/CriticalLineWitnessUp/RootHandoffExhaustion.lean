import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_handoff_exhaustion
    {Z S M R Q H C P N rootRead handoff : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q rootRead ->
        Cont rootRead C handoff ->
          SemanticNameCert
              (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
              (fun row : BHist => hsame row handoff ∧ Cont (append Z S) Q rootRead)
              (fun row : BHist => hsame row handoff ∧ Cont rootRead C handoff)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory C ∧
              UnaryHistory N ∧ UnaryHistory rootRead ∧ UnaryHistory handoff ∧
                hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                  Cont (append Z S) Q rootRead ∧ Cont rootRead C handoff := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet rootRoute handoffRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed unaryAppend unaryQ rootRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed rootUnary unaryC handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
          (fun row : BHist => hsame row handoff ∧ Cont (append Z S) Q rootRead)
          (fun row : BHist => hsame row handoff ∧ Cont rootRead C handoff)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff ⟨hsame_refl handoff, handoffUnary⟩
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
      exact ⟨source.left, rootRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, handoffRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryC, unaryN, rootUnary, handoffUnary, sameH,
      routeQ, routeC, routeN, rootRoute, handoffRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
