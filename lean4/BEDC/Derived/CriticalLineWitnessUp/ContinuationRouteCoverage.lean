import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_continuation_route_coverage
    {Z S M R Q H C P N sourceRead comparisonRead packageRead downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont Q H comparisonRead ->
          Cont C P packageRead ->
            Cont sourceRead packageRead downstreamRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row downstreamRead ∧ Cont sourceRead packageRead downstreamRead)
                  (fun row : BHist =>
                    hsame row downstreamRead ∧ Cont C P packageRead)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory Q ∧
                  UnaryHistory sourceRead ∧ UnaryHistory comparisonRead ∧
                    UnaryHistory packageRead ∧ UnaryHistory downstreamRead ∧
                      hsame H (append Z S) ∧ Cont Z S sourceRead ∧
                        Cont Q H comparisonRead ∧ Cont C P packageRead ∧
                          Cont sourceRead packageRead downstreamRead ∧ Cont M R Q ∧
                            Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute comparisonRoute packageRoute downstreamRoute
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
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryQ unaryH comparisonRoute
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed unaryC unaryP packageRoute
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed sourceUnary packageUnary downstreamRoute
  have sourceAtDownstream : hsame downstreamRead downstreamRead ∧ UnaryHistory downstreamRead :=
    ⟨hsame_refl downstreamRead, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont sourceRead packageRead downstreamRead)
          (fun row : BHist => hsame row downstreamRead ∧ Cont C P packageRead)
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
      exact ⟨source.left, downstreamRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, packageRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryQ, sourceUnary, comparisonUnary, packageUnary,
      downstreamUnary, sameH, sourceRoute, comparisonRoute, packageRoute, downstreamRoute,
      routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
