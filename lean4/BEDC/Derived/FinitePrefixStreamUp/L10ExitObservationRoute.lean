import BEDC.Derived.FinitePrefixStreamUp.CompletionSectionPullback

namespace BEDC.Derived.FinitePrefixStreamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem FinitePrefixStreamL10ExitObservationRoute
    {k W D R H C P N windowRead regularRead completionRead sectionRead : BHist} :
    FinitePrefixStreamCarrier k W D R H C P N →
      Cont k W windowRead →
        Cont windowRead D regularRead →
          Cont regularRead R completionRead →
            Cont D R sectionRead →
              Nonempty (NameCert (fun row : BHist => hsame row sectionRead) hsame) →
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                        hsame row regularRead ∨ hsame row completionRead)
                    (fun row : BHist =>
                      hsame row completionRead ∧ Cont regularRead R completionRead)
                    hsame ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row sectionRead)
                    (fun row : BHist =>
                      hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row sectionRead)
                    (fun row : BHist =>
                      hsame row sectionRead ∧ Cont D R sectionRead)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert SemanticNameCert UnaryHistory
  intro carrier windowRoute regularRoute completionRoute sectionRoute sectionCert
  have completionPack :=
    FinitePrefixStreamCarrier_real_completion_budget_route
      (k := k) (W := W) (D := D) (R := R) (H := H) (C := C) (P := P) (N := N)
      (windowRead := windowRead) (regularRead := regularRead)
      (completionRead := completionRead)
      carrier windowRoute regularRoute completionRoute
  have completionCert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row regularRead ∨ hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ Cont regularRead R completionRead)
          hsame :=
    completionPack.left
  have sectionCertOut :
      SemanticNameCert
          (fun row : BHist => hsame row sectionRead)
          (fun row : BHist =>
            hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row sectionRead)
          (fun row : BHist => hsame row sectionRead ∧ Cont D R sectionRead)
          hsame :=
    by
      cases sectionCert with
      | intro sectionCore =>
          exact {
            core := {
              carrier_inhabited := sectionCore.carrier_inhabited
              equiv_refl := by
                intro row source
                exact hsame_trans (sectionCore.equiv_refl source) (hsame_refl row)
              equiv_symm := by
                intro _row _other sameRows
                exact sectionCore.equiv_symm sameRows
              equiv_trans := by
                intro _row _middle _other sameLeft sameRight
                exact sectionCore.equiv_trans sameLeft sameRight
              carrier_respects_equiv := by
                intro _row _other sameRows source
                exact sectionCore.carrier_respects_equiv sameRows source
            }
            pattern_sound := by
              intro _row source
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr source)))))))
            ledger_sound := by
              intro _row source
              exact ⟨source, sectionRoute⟩
          }
  exact ⟨completionCert, sectionCertOut⟩

end BEDC.Derived.FinitePrefixStreamUp
