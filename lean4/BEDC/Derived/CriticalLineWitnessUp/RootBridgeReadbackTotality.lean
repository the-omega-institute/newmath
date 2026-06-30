import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_bridge_readback_totality
    {Z S M R Q H C P N bridgeRead comparisonRead localRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S bridgeRead ->
        Cont M R comparisonRead ->
          Cont bridgeRead comparisonRead localRead ->
            SemanticNameCert
                (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row localRead)
                (fun row : BHist => hsame row localRead ∧
                  Cont bridgeRead comparisonRead localRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory bridgeRead ∧ UnaryHistory comparisonRead ∧
                  UnaryHistory localRead ∧ hsame comparisonRead Q ∧
                    hsame H (append Z S) ∧ Cont Z S bridgeRead ∧
                      Cont M R comparisonRead ∧ Cont bridgeRead comparisonRead localRead ∧
                        Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet bridgeRoute comparisonRoute localRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed unaryZ unaryS bridgeRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed bridgeUnary comparisonUnary localRoute
  have comparisonSameQ : hsame comparisonRead Q :=
    cont_deterministic comparisonRoute routeQ
  have sourceAtLocal : hsame localRead localRead ∧ UnaryHistory localRead :=
    ⟨hsame_refl localRead, localUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row localRead)
          (fun row : BHist => hsame row localRead ∧
            Cont bridgeRead comparisonRead localRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localRead sourceAtLocal
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
      exact ⟨source.left, localRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, bridgeUnary, comparisonUnary,
      localUnary, comparisonSameQ, sameH, bridgeRoute, comparisonRoute, localRoute, routeQ,
      routeC, routeN⟩

theorem CriticalLineWitnessRootAnalyticRefusalExhaustion
    {Z S M R Q H C P N refusalRead analyticRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead C analyticRead ->
          SemanticNameCert
              (fun row : BHist => hsame row analyticRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row analyticRead ∧ Cont N Q refusalRead)
              (fun row : BHist => hsame row analyticRead ∧ Cont refusalRead C analyticRead)
              hsame ∧
            UnaryHistory analyticRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
              Cont Q H C ∧ Cont C P N ∧ Cont N Q refusalRead ∧
                Cont refusalRead C analyticRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute analyticRoute
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
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have analyticUnary : UnaryHistory analyticRead :=
    unary_cont_closed refusalUnary unaryC analyticRoute
  have sourceAtAnalytic : hsame analyticRead analyticRead ∧ UnaryHistory analyticRead :=
    ⟨hsame_refl analyticRead, analyticUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row analyticRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row analyticRead ∧ Cont N Q refusalRead)
          (fun row : BHist => hsame row analyticRead ∧ Cont refusalRead C analyticRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro analyticRead sourceAtAnalytic
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
      exact ⟨source.left, refusalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, analyticRoute⟩
  }
  exact
    ⟨cert, analyticUnary, sameH, routeQ, routeC, routeN, refusalRoute, analyticRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
