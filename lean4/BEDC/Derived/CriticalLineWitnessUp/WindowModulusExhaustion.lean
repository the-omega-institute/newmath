import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_window_zero_locator_route
    {Z S M R Q H C P N sourceWindow zeroLocator : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont (append Z S) M sourceWindow →
        Cont sourceWindow N zeroLocator →
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory Q ∧
            UnaryHistory sourceWindow ∧ UnaryHistory zeroLocator ∧
              hsame H (append Z S) ∧ Cont M R Q ∧
                Cont (append Z S) M sourceWindow ∧ Cont sourceWindow N zeroLocator ∧
                  Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sourceWindowRoute zeroLocatorRoute
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
  have sourceWindowUnary : UnaryHistory sourceWindow :=
    unary_cont_closed unaryAppend unaryM sourceWindowRoute
  have zeroLocatorUnary : UnaryHistory zeroLocator :=
    unary_cont_closed sourceWindowUnary unaryN zeroLocatorRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryQ, sourceWindowUnary, zeroLocatorUnary, sameH, routeQ,
      sourceWindowRoute, zeroLocatorRoute, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_window_modulus_exhaustion
    {Z S M R Q H C P N sourceRead modulusRead downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q sourceRead ->
        Cont M R modulusRead ->
          Cont sourceRead modulusRead downstreamRead ->
            SemanticNameCert
                (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row downstreamRead)
                (fun row : BHist =>
                  hsame row downstreamRead ∧ Cont sourceRead modulusRead downstreamRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory sourceRead ∧
                  UnaryHistory modulusRead ∧ UnaryHistory downstreamRead ∧
                    hsame H (append Z S) ∧ Cont (append Z S) Q sourceRead ∧
                      Cont M R modulusRead ∧ Cont sourceRead modulusRead downstreamRead ∧
                        Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute downstreamRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceBaseUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceBaseUnary (hsame_symm sameH)
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceBaseUnary unaryQ sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed sourceUnary modulusUnary downstreamRoute
  have sourceAtDownstream : hsame downstreamRead downstreamRead ∧ UnaryHistory downstreamRead :=
    ⟨hsame_refl downstreamRead, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row downstreamRead)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont sourceRead modulusRead downstreamRead)
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, downstreamRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, sourceUnary, modulusUnary,
      downstreamUnary, sameH, sourceRoute, modulusRoute, downstreamRoute, routeQ, routeC,
      routeN⟩

theorem CriticalLineWitnessCarrier_zero_localization_obligation
    {Z S M R Q H C P N zeroRead realRead localRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont M R realRead ->
          Cont zeroRead realRead localRead ->
            SemanticNameCert
                (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row localRead)
                (fun row : BHist =>
                  hsame row localRead ∧ Cont zeroRead realRead localRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory zeroRead ∧ UnaryHistory realRead ∧
                  UnaryHistory localRead ∧ hsame H (append Z S) ∧ Cont Z S zeroRead ∧
                    Cont M R realRead ∧ Cont zeroRead realRead localRead ∧
                      Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute realRoute localRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed unaryM unaryR realRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed zeroUnary realUnary localRoute
  have sourceAtLocal : hsame localRead localRead ∧ UnaryHistory localRead :=
    ⟨hsame_refl localRead, localUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row localRead)
          (fun row : BHist => hsame row localRead ∧ Cont zeroRead realRead localRead)
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
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, zeroUnary, realUnary, localUnary,
      sameH, zeroRoute, realRoute, localRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
