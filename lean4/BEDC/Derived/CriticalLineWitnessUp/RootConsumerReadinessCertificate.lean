import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_consumer_readiness_certificate
    {Z S M R Q H C P N classifierRead ledgerRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q classifierRead ->
        Cont M R ledgerRead ->
          Cont classifierRead ledgerRead consumerRead ->
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row consumerRead ∧ Cont (append Z S) Q classifierRead ∧
                    Cont M R ledgerRead)
                (fun row : BHist =>
                  hsame row consumerRead ∧ Cont classifierRead ledgerRead consumerRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory classifierRead ∧
                  UnaryHistory ledgerRead ∧ UnaryHistory consumerRead ∧
                    hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                      Cont (append Z S) Q classifierRead ∧ Cont M R ledgerRead ∧
                        Cont classifierRead ledgerRead consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet classifierRoute ledgerRoute consumerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed unaryAppend unaryQ classifierRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed unaryM unaryR ledgerRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed classifierUnary ledgerUnary consumerRoute
  have sourceAtConsumer : hsame consumerRead consumerRead ∧ UnaryHistory consumerRead :=
    ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row consumerRead ∧ Cont (append Z S) Q classifierRead ∧
              Cont M R ledgerRead)
          (fun row : BHist =>
            hsame row consumerRead ∧ Cont classifierRead ledgerRead consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
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
      exact ⟨source.left, classifierRoute, ledgerRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, classifierUnary, ledgerUnary,
      consumerUnary, sameH, routeQ, routeC, routeN, classifierRoute, ledgerRoute,
      consumerRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
