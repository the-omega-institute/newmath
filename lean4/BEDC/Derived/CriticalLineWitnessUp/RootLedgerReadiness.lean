import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_ledger_readiness
    {Z S M R Q H C P N ledgerRead supportRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R ledgerRead ->
        Cont ledgerRead H supportRead ->
          SemanticNameCert
              (fun row : BHist => hsame row supportRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row supportRead ∧ Cont M R ledgerRead)
              (fun row : BHist =>
                hsame row supportRead ∧ Cont M R ledgerRead ∧
                  Cont ledgerRead H supportRead)
              hsame ∧
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧
              UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory ledgerRead ∧
                UnaryHistory supportRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet ledgerRoute supportRoute
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
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed unaryM unaryR ledgerRoute
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed ledgerUnary unaryH supportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row supportRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row supportRead ∧ Cont M R ledgerRead)
          (fun row : BHist =>
            hsame row supportRead ∧ Cont M R ledgerRead ∧ Cont ledgerRead H supportRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro supportRead ⟨hsame_refl supportRead, supportUnary⟩
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
      exact ⟨source.left, ledgerRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerRoute, supportRoute⟩
  }
  exact
    ⟨cert, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN, ledgerUnary, supportUnary,
      sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
