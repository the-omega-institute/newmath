import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_continuation_zero_strip_coherence
    {Z S M R Q H C P N zeroStripRead continuationRead handoffRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont zeroStripRead H continuationRead ->
          Cont continuationRead N handoffRead ->
            SemanticNameCert
                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row H ∨
                    hsame row C ∨ hsame row N ∨ hsame row zeroStripRead ∨
                      hsame row continuationRead ∨ hsame row handoffRead)
                (fun row : BHist =>
                  hsame row handoffRead ∧ Cont zeroStripRead H continuationRead ∧
                    Cont continuationRead N handoffRead)
                hsame ∧
              UnaryHistory zeroStripRead ∧ UnaryHistory continuationRead ∧
                UnaryHistory handoffRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripRoute continuationRoute handoffRoute
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
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have continuationUnary : UnaryHistory continuationRead :=
    unary_cont_closed zeroStripUnary unaryH continuationRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed continuationUnary unaryN handoffRoute
  have sourceHandoff :
      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
              hsame row N ∨ hsame row zeroStripRead ∨ hsame row continuationRead ∨
                hsame row handoffRead)
          (fun row : BHist =>
            hsame row handoffRead ∧ Cont zeroStripRead H continuationRead ∧
              Cont continuationRead N handoffRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoff
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, continuationRoute, handoffRoute⟩
  }
  exact ⟨cert, zeroStripUnary, continuationUnary, handoffUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
