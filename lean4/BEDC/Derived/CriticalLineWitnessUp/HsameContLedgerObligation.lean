import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_hsame_cont_ledger_obligation
    {Z S M R Q H C P N replayRead localRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q H replayRead ->
        Cont replayRead N localRead ->
          SemanticNameCert
              (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Q ∨ hsame row H ∨ hsame row replayRead ∨ hsame row N ∨
                  hsame row localRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont Q H replayRead ∧ Cont replayRead N localRead)
              hsame ∧ UnaryHistory replayRead ∧ UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet replayRoute localRoute
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
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed unaryQ unaryH replayRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed replayUnary unaryN localRoute
  refine ⟨?_, replayUnary, localUnary⟩
  refine
    { core :=
        { carrier_inhabited := ⟨localRead, hsame_refl localRead, localUnary⟩
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows sourceRow
    exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
      unary_transport sourceRow.right sameRows⟩
  · intro _row sourceRow
    exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
  · intro _row sourceRow
    exact ⟨sourceRow.right, replayRoute, localRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
