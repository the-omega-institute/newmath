import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_localization_source_window
    {Z S M R Q H C P N zeroRead realRead sourceWindow localRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont M R realRead ->
          Cont zeroRead realRead sourceWindow ->
            Cont sourceWindow Q localRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row localRead /\ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row zeroRead \/ hsame row realRead \/ hsame row sourceWindow \/
                      hsame row localRead)
                  (fun row : BHist => hsame row localRead /\ Cont sourceWindow Q localRead)
                  hsame /\
                UnaryHistory zeroRead /\ UnaryHistory realRead /\
                  UnaryHistory sourceWindow /\ UnaryHistory localRead /\
                    hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute realRoute sourceWindowRoute localRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZeroRead : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have unaryRealRead : UnaryHistory realRead :=
    unary_cont_closed unaryM unaryR realRoute
  have unarySourceWindow : UnaryHistory sourceWindow :=
    unary_cont_closed unaryZeroRead unaryRealRead sourceWindowRoute
  have unaryLocalRead : UnaryHistory localRead :=
    unary_cont_closed unarySourceWindow unaryQ localRoute
  have sourceAtLocal : hsame localRead localRead /\ UnaryHistory localRead :=
    ⟨hsame_refl localRead, unaryLocalRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row zeroRead \/ hsame row realRead \/ hsame row sourceWindow \/
              hsame row localRead)
          (fun row : BHist => hsame row localRead /\ Cont sourceWindow Q localRead)
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, localRoute⟩
  }
  exact
    ⟨cert, unaryZeroRead, unaryRealRead, unarySourceWindow, unaryLocalRead, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
