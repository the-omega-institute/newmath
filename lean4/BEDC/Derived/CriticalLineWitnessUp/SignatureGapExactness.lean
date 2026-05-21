import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_signature_gap_exactness
    {Z S M R Q H C P N zeroStripRead comparisonRead replayRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont M R comparisonRead ->
          Cont comparisonRead H replayRead ->
            SemanticNameCert
                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row replayRead)
                (fun row : BHist => hsame row replayRead ∧ Cont comparisonRead H replayRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory zeroStripRead ∧
                  UnaryHistory comparisonRead ∧ UnaryHistory replayRead ∧
                    hsame H (append Z S) ∧ Cont Z S zeroStripRead ∧ Cont M R Q ∧
                      Cont M R comparisonRead ∧ Cont comparisonRead H replayRead ∧
                        Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripRoute comparisonRoute replayRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed comparisonUnary unaryH replayRoute
  have sourceAtReplay : hsame replayRead replayRead ∧ UnaryHistory replayRead :=
    ⟨hsame_refl replayRead, replayUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row replayRead)
          (fun row : BHist => hsame row replayRead ∧ Cont comparisonRead H replayRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead sourceAtReplay
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
      exact ⟨source.left, replayRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, zeroStripUnary,
      comparisonUnary, replayUnary, sameH, zeroStripRoute, routeQ, comparisonRoute,
      replayRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
