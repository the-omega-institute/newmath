import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionHistoryLedgerPolicy_exclusive_readback {source : BHist -> Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {raw visible : BHist} :
    OptionHistoryLedgerPolicy source raw visible ->
      ((hsame raw BHist.Empty ∧ hsame visible BHist.Empty ∧ (source raw -> False) ∧
          (source visible -> False)) ∨
        (source raw ∧ source visible ∧ (hsame raw BHist.Empty -> False) ∧
          (hsame visible BHist.Empty -> False) ∧ hsame raw visible)) := by
  intro ledger
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      have rawReadback := OptionHistoryCarrier_exclusive_readback sourceExcludesEmpty rawCarrier
      cases rawReadback with
      | inl absentRaw =>
          have visibleEmpty : hsame visible BHist.Empty :=
            hsame_trans (hsame_symm sameRawVisible) absentRaw.left
          exact Or.inl
            (And.intro absentRaw.left
              (And.intro visibleEmpty
                (And.intro absentRaw.right
                  (by
                    intro visibleSource
                    exact sourceExcludesEmpty visible visibleSource visibleEmpty))))
      | inr presentRaw =>
          have visibleSource : source visible := by
            cases sameRawVisible
            exact presentRaw.left
          have visibleNotEmpty : hsame visible BHist.Empty -> False := by
            intro visibleEmpty
            exact presentRaw.right (hsame_trans sameRawVisible visibleEmpty)
          exact Or.inr
            (And.intro presentRaw.left
              (And.intro visibleSource
                (And.intro presentRaw.right
                  (And.intro visibleNotEmpty sameRawVisible))))

end BEDC.Derived.OptionUp
