import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_budget_transport
    {Z S M R Q H C P N zeroBudget downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroBudget ->
        Cont zeroBudget N downstreamRead ->
          SemanticNameCert
              (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row downstreamRead ∧ Cont Z S zeroBudget)
              (fun row : BHist => hsame row downstreamRead ∧
                Cont zeroBudget N downstreamRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory N ∧
                UnaryHistory zeroBudget ∧ UnaryHistory downstreamRead ∧
                  hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧
                    Cont C P N ∧ Cont Z S zeroBudget ∧
                      Cont zeroBudget N downstreamRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute downstreamRoute
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
  have unaryZeroBudget : UnaryHistory zeroBudget :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have unaryDownstreamRead : UnaryHistory downstreamRead :=
    unary_cont_closed unaryZeroBudget unaryN downstreamRoute
  have sourceAtDownstream : hsame downstreamRead downstreamRead ∧
      UnaryHistory downstreamRead :=
    ⟨hsame_refl downstreamRead, unaryDownstreamRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row downstreamRead ∧ Cont Z S zeroBudget)
          (fun row : BHist => hsame row downstreamRead ∧
            Cont zeroBudget N downstreamRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstreamRead sourceAtDownstream
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
      exact ⟨source.left, zeroRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, downstreamRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryN,
      unaryZeroBudget, unaryDownstreamRead, sameH, routeQ, routeC, routeN, zeroRoute,
      downstreamRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
