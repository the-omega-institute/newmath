import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_zeta_refusal_ledger
    {Z S M R Q H C P N stripRead phaseReal regSeq budgetRead zetaLedger : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead M phaseReal ->
          Cont phaseReal C regSeq ->
            Cont regSeq N budgetRead ->
              Cont budgetRead Q zetaLedger ->
                SemanticNameCert
                    (fun row : BHist => hsame row zetaLedger ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                        hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row stripRead ∨ hsame row phaseReal ∨
                            hsame row regSeq ∨ hsame row budgetRead ∨
                              hsame row zetaLedger)
                    (fun row : BHist =>
                      hsame row zetaLedger ∧ Cont Z S stripRead ∧
                        Cont stripRead M phaseReal ∧ Cont phaseReal C regSeq ∧
                          Cont regSeq N budgetRead ∧ Cont budgetRead Q zetaLedger)
                    hsame ∧ UnaryHistory zetaLedger ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute phaseRoute regSeqRoute budgetRoute zetaLedgerRoute
  have carrierPacket := packet
  obtain ⟨unaryZ, unaryS, unaryM, _unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure carrierPacket
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have phaseUnary : UnaryHistory phaseReal :=
    unary_cont_closed stripUnary unaryM phaseRoute
  have regSeqUnary : UnaryHistory regSeq :=
    unary_cont_closed phaseUnary routeClosure.right.left regSeqRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed regSeqUnary routeClosure.right.right.left budgetRoute
  have zetaLedgerUnary : UnaryHistory zetaLedger :=
    unary_cont_closed budgetUnary routeClosure.left zetaLedgerRoute
  have sourceZetaLedger :
      (fun row : BHist => hsame row zetaLedger ∧ UnaryHistory row) zetaLedger := by
    exact ⟨hsame_refl zetaLedger, zetaLedgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zetaLedger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row stripRead ∨ hsame row phaseReal ∨ hsame row regSeq ∨
                  hsame row budgetRead ∨ hsame row zetaLedger)
          (fun row : BHist =>
            hsame row zetaLedger ∧ Cont Z S stripRead ∧ Cont stripRead M phaseReal ∧
              Cont phaseReal C regSeq ∧ Cont regSeq N budgetRead ∧
                Cont budgetRead Q zetaLedger)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zetaLedger sourceZetaLedger
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
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, stripRoute, phaseRoute, regSeqRoute, budgetRoute,
          zetaLedgerRoute⟩
  }
  exact ⟨cert, zetaLedgerUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
