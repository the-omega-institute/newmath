import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_consumer_determinacy
    {Z S M R Q H C P N phaseRead classifierRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont R Q phaseRead ->
        Cont phaseRead H classifierRead ->
          Cont classifierRead N consumerRead ->
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row N ∨
                    hsame row phaseRead ∨ hsame row classifierRead ∨ hsame row consumerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont R Q phaseRead ∧ Cont phaseRead H classifierRead ∧
                    Cont classifierRead N consumerRead)
                hsame ∧
              UnaryHistory phaseRead ∧ UnaryHistory classifierRead ∧
                UnaryHistory consumerRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet phaseRoute classifierRoute consumerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed unaryR unaryQ phaseRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed phaseUnary unaryH classifierRoute
  have unaryN : UnaryHistory N := by
    have unaryC : UnaryHistory C :=
      unary_cont_closed unaryQ unaryH routeC
    exact unary_cont_closed unaryC _unaryP routeN
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed classifierUnary unaryN consumerRoute
  have sourceAtConsumer : hsame consumerRead consumerRead ∧ UnaryHistory consumerRead :=
    ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row N ∨
              hsame row phaseRead ∨ hsame row classifierRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R Q phaseRead ∧ Cont phaseRead H classifierRead ∧
              Cont classifierRead N consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
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
      exact ⟨source.right, phaseRoute, classifierRoute, consumerRoute⟩
  }
  exact
    ⟨cert, phaseUnary, classifierUnary, consumerUnary, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
