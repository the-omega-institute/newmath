import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_finite_observation_route
    {Z S M R Q H C P N zeroStripRead comparisonRead rootRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zeroStripRead →
        Cont R Q comparisonRead →
          Cont zeroStripRead comparisonRead rootRead →
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory Q ∧
              UnaryHistory zeroStripRead ∧ UnaryHistory comparisonRead ∧
                UnaryHistory rootRead ∧ hsame H (append Z S) ∧ Cont Z S zeroStripRead ∧
                  Cont R Q comparisonRead ∧ Cont zeroStripRead comparisonRead rootRead ∧
                    Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zeroStripRoute comparisonRoute rootRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZeroStripRead : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have unaryComparisonRead : UnaryHistory comparisonRead :=
    unary_cont_closed unaryR unaryQ comparisonRoute
  have unaryRootRead : UnaryHistory rootRead :=
    unary_cont_closed unaryZeroStripRead unaryComparisonRead rootRoute
  exact
    ⟨unaryZ, unaryS, unaryR, unaryQ, unaryZeroStripRead, unaryComparisonRead,
      unaryRootRead, sameH, zeroStripRoute, comparisonRoute, rootRoute, routeQ, routeC,
      routeN⟩

theorem CriticalLineWitnessCarrier_stdbridge_candidate_refusal
    {Z S M R Q H C P N bridgeRead refusalRead failedCandidate : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont (append Z S) Q bridgeRead →
        Cont N Q refusalRead →
          Cont refusalRead bridgeRead failedCandidate →
            SemanticNameCert
                (fun row : BHist => hsame row failedCandidate ∧ UnaryHistory row)
                (fun row : BHist => hsame row failedCandidate)
                (fun row : BHist =>
                  hsame row failedCandidate ∧ Cont refusalRead bridgeRead failedCandidate)
                hsame ∧
              UnaryHistory bridgeRead ∧ UnaryHistory refusalRead ∧
                UnaryHistory failedCandidate ∧ hsame H (append Z S) ∧
                  Cont (append Z S) Q bridgeRead ∧ Cont N Q refusalRead ∧
                    Cont refusalRead bridgeRead failedCandidate := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert UnaryHistory
  intro packet bridgeRoute refusalRoute failedRoute
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
  have unaryBridgeRead : UnaryHistory bridgeRead :=
    unary_cont_closed (unary_cont_closed unaryZ unaryS (cont_intro rfl)) unaryQ bridgeRoute
  have unaryRefusalRead : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have unaryFailedCandidate : UnaryHistory failedCandidate :=
    unary_cont_closed unaryRefusalRead unaryBridgeRead failedRoute
  have sourceAtFailed : hsame failedCandidate failedCandidate ∧ UnaryHistory failedCandidate :=
    ⟨hsame_refl failedCandidate, unaryFailedCandidate⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row failedCandidate ∧ UnaryHistory row)
          (fun row : BHist => hsame row failedCandidate)
          (fun row : BHist =>
            hsame row failedCandidate ∧ Cont refusalRead bridgeRead failedCandidate)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro failedCandidate sourceAtFailed
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, failedRoute⟩
  }
  exact
    ⟨cert, unaryBridgeRead, unaryRefusalRead, unaryFailedCandidate, sameH, bridgeRoute,
      refusalRoute, failedRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
