import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_namecert_obligation_completion
    {Z S M R Q H C P N refusalRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead C boundaryRead ->
          SemanticNameCert
              (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row boundaryRead)
              (fun row : BHist => hsame row boundaryRead ∧ Cont refusalRead C boundaryRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧
                UnaryHistory refusalRead ∧ UnaryHistory boundaryRead ∧ hsame H (append Z S) ∧
                  Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont N Q refusalRead ∧
                    Cont refusalRead C boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute boundaryRoute
  exact CriticalLineWitnessCarrier_root_unblock_refusal_boundary packet refusalRoute boundaryRoute

end BEDC.Derived.CriticalLineWitnessUp
