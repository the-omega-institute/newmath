import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_consumer_handoff
    {Z S M R Q H C P N sourceRead modulusRead handoff : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R modulusRead ->
          Cont sourceRead modulusRead handoff ->
            SemanticNameCert
                (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row handoff ∧ Cont Z S sourceRead ∧ Cont M R modulusRead)
                (fun row : BHist =>
                  hsame row handoff ∧ Cont sourceRead modulusRead handoff)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory handoff ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                    Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute handoffRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unarySourceRead : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unaryHandoff : UnaryHistory handoff :=
    unary_cont_closed unarySourceRead unaryModulusRead handoffRoute
  have sourceAtHandoff : hsame handoff handoff ∧ UnaryHistory handoff :=
    ⟨hsame_refl handoff, unaryHandoff⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row handoff ∧ Cont Z S sourceRead ∧ Cont M R modulusRead)
          (fun row : BHist =>
            hsame row handoff ∧ Cont sourceRead modulusRead handoff)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff sourceAtHandoff
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
      exact ⟨source.left, sourceRoute, modulusRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, handoffRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unarySourceRead, unaryModulusRead,
      unaryHandoff, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
