import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_zeta_source_factorization
    {Z S M R Q H C P N zetaRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead N consumerRead ->
          SemanticNameCert
              (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row consumerRead ∧ Cont Z S zetaRead)
              (fun row : BHist => hsame row consumerRead ∧ Cont zetaRead N consumerRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory C ∧
              UnaryHistory N ∧ UnaryHistory zetaRead ∧ UnaryHistory consumerRead ∧
                hsame H (append Z S) ∧ Cont Z S zetaRead ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N ∧ Cont zetaRead N consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute consumerRoute
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
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed zetaUnary unaryN consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row consumerRead ∧ Cont Z S zetaRead)
          (fun row : BHist => hsame row consumerRead ∧ Cont zetaRead N consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead
        ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact ⟨source.left, zetaRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryC, unaryN, zetaUnary, consumerUnary, sameH,
      zetaRoute, routeQ, routeC, routeN, consumerRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
