import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist

namespace BEDC.Derived.BundleUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

def BundleLocalTrivPkg (base total projection fibre ledger : BHist)
    (triv transitions : ProbeBundle BHist) : ProbeBundle BHist :=
  ProbeBundle.Bcons base
    (ProbeBundle.Bcons total
      (ProbeBundle.Bcons projection
        (ProbeBundle.Bcons fibre
          (bundleAppend triv (ProbeBundle.Bcons ledger transitions)))))

theorem BundleLocalTrivPkg_projection_rows {base total projection fibre ledger row : BHist}
    {triv transitions : ProbeBundle BHist} :
    InBundle row (BundleLocalTrivPkg base total projection fibre ledger triv transitions) ->
      row = base ∨ row = total ∨ row = projection ∨ row = fibre ∨ InBundle row triv ∨
        row = ledger ∨ InBundle row transitions := by
  intro member
  cases member with
  | inl sameBase =>
      exact Or.inl sameBase
  | inr memberTotalTail =>
      cases memberTotalTail with
      | inl sameTotal =>
          exact Or.inr (Or.inl sameTotal)
      | inr memberProjectionTail =>
          cases memberProjectionTail with
          | inl sameProjection =>
              exact Or.inr (Or.inr (Or.inl sameProjection))
          | inr memberFibreTail =>
              cases memberFibreTail with
              | inl sameFibre =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl sameFibre)))
              | inr memberTail =>
                  cases Iff.mp inBundle_bundleAppend_iff memberTail with
                  | inl memberTriv =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl memberTriv))))
                  | inr memberLedgerTail =>
                      cases memberLedgerTail with
                      | inl sameLedger =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr (Or.inl sameLedger)))))
                      | inr memberTransitions =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr (Or.inr memberTransitions)))))

theorem BundleLocalTrivPkg_trivialization_scope {base total projection fibre ledger row : BHist}
    {triv transitions : ProbeBundle BHist} :
    InBundle row triv ->
      InBundle row (BundleLocalTrivPkg base total projection fibre ledger triv transitions) := by
  intro memberTriv
  exact Or.inr
    (Or.inr
      (Or.inr
        (Or.inr
          (Iff.mpr inBundle_bundleAppend_iff (Or.inl memberTriv)))))

end BEDC.Derived.BundleUp
