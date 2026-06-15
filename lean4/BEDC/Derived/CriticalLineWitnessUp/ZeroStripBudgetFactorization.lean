import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_budget_factorization
    {Z S M R Q H C P N zeroBudget modulusRead downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroBudget ->
        Cont zeroBudget Q modulusRead ->
          Cont modulusRead N downstreamRead ->
            SemanticNameCert
                (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row downstreamRead ∧ Cont Z S zeroBudget ∧
                    Cont zeroBudget Q modulusRead)
                (fun row : BHist =>
                  hsame row downstreamRead ∧ Cont modulusRead N downstreamRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory zeroBudget ∧ UnaryHistory modulusRead ∧
                  UnaryHistory downstreamRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                    Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute modulusRoute downstreamRoute
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
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryZeroBudget unaryQ modulusRoute
  have unaryDownstreamRead : UnaryHistory downstreamRead :=
    unary_cont_closed unaryModulusRead unaryN downstreamRoute
  have sourceAtDownstream : hsame downstreamRead downstreamRead ∧
      UnaryHistory downstreamRead :=
    ⟨hsame_refl downstreamRead, unaryDownstreamRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont Z S zeroBudget ∧
              Cont zeroBudget Q modulusRead)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont modulusRead N downstreamRead)
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
      exact ⟨source.left, zeroRoute, modulusRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, downstreamRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryZeroBudget, unaryModulusRead,
      unaryDownstreamRead, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
