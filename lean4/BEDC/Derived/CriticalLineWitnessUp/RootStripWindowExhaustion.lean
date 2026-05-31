import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_strip_window_exhaustion
    {Z S M R Q H C P N stripWindow selectorRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) H stripWindow ->
        Cont stripWindow N selectorRead ->
          SemanticNameCert
              (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row selectorRead ∧
                Cont (append Z S) H stripWindow)
              (fun row : BHist => hsame row selectorRead ∧
                Cont stripWindow N selectorRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory N ∧
                UnaryHistory stripWindow ∧ UnaryHistory selectorRead ∧
                  hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧
                    Cont C P N ∧ Cont (append Z S) H stripWindow ∧
                      Cont stripWindow N selectorRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet windowRoute selectorRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppendZS : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppendZS (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unaryStripWindow : UnaryHistory stripWindow :=
    unary_cont_closed unaryAppendZS unaryH windowRoute
  have unarySelectorRead : UnaryHistory selectorRead :=
    unary_cont_closed unaryStripWindow unaryN selectorRoute
  have sourceAtSelector : hsame selectorRead selectorRead ∧ UnaryHistory selectorRead :=
    ⟨hsame_refl selectorRead, unarySelectorRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row selectorRead ∧
            Cont (append Z S) H stripWindow)
          (fun row : BHist => hsame row selectorRead ∧ Cont stripWindow N selectorRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro selectorRead sourceAtSelector
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
      exact ⟨source.left, windowRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, selectorRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryN, unaryStripWindow,
      unarySelectorRead, sameH, routeQ, routeC, routeN, windowRoute, selectorRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
