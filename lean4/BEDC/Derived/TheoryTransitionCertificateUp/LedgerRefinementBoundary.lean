import BEDC.Derived.TheoryTransitionCertificateUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TheoryTransitionCertificateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TheoryTransitionCertificateLedgerRefinementBoundary
    {T1 T2 S C D L F H R P N preservedRead ledgerFailure boundaryRead : BHist} :
    Cont S D preservedRead →
      Cont L F ledgerFailure →
        Cont preservedRead ledgerFailure boundaryRead →
          theoryTransitionCertificateFields
              (TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N) =
            [T1, T2, S, C, D, L, F, H, R, P, N] ∧
          Cont S D preservedRead ∧
            Cont L F ledgerFailure ∧
              Cont preservedRead ledgerFailure boundaryRead ∧
                SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead)
                  (fun row : BHist =>
                    hsame row preservedRead ∨
                      hsame row ledgerFailure ∨ hsame row boundaryRead)
                  (fun row : BHist =>
                    hsame row boundaryRead ∧ Cont L F ledgerFailure)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame
  intro preservedRoute ledgerRoute boundaryRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row boundaryRead)
        (fun row : BHist =>
          hsame row preservedRead ∨ hsame row ledgerFailure ∨ hsame row boundaryRead)
        (fun row : BHist => hsame row boundaryRead ∧ Cont L F ledgerFailure)
        hsame := by
    exact {
      core := {
        carrier_inhabited := ⟨boundaryRead, hsame_refl boundaryRead⟩
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
          exact hsame_trans (hsame_symm sameRows) source
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source)
      ledger_sound := by
        intro _row source
        exact ⟨source, ledgerRoute⟩
    }
  exact ⟨rfl, preservedRoute, ledgerRoute, boundaryRoute, cert⟩

end BEDC.Derived.TheoryTransitionCertificateUp
