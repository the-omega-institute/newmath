import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_supplied_zero_strip_route
    {Z S M R Q H C P N zeroStripRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        SemanticNameCert
            (fun row : BHist => hsame row zeroStripRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row zeroStripRead)
            (fun row : BHist => hsame row zeroStripRead ∧ Cont Z S zeroStripRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
            UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory zeroStripRead ∧
              hsame H (append Z S) ∧ Cont Z S zeroStripRead ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have sameZeroStripH : hsame zeroStripRead H :=
    hsame_trans zeroStripRoute (hsame_symm sameH)
  have unaryH : UnaryHistory H :=
    unary_transport zeroStripUnary sameZeroStripH
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have sourceAtZeroStrip : hsame zeroStripRead zeroStripRead ∧ UnaryHistory zeroStripRead :=
    ⟨hsame_refl zeroStripRead, zeroStripUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zeroStripRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row zeroStripRead)
          (fun row : BHist => hsame row zeroStripRead ∧ Cont Z S zeroStripRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zeroStripRead sourceAtZeroStrip
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
      exact ⟨source.left, zeroStripRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryH, unaryC, unaryP, unaryN, zeroStripUnary, sameH,
      zeroStripRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
