import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BundleUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BundleRowsUnary : ProbeBundle BHist -> Prop
  | .Bnil => True
  | .Bcons row tail => UnaryHistory row ∧ BundleRowsUnary tail

def BundleLocalTrivPackage
    (base total projection fiber : BHist) (trivs transitions : ProbeBundle BHist)
    (ledger : BHist) : Prop :=
  UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fiber ∧
    UnaryHistory ledger ∧ BundleRowsUnary trivs ∧ BundleRowsUnary transitions

theorem BundleLocalTrivPackage_carrier_projection
    {base total projection fiber ledger : BHist} {trivs transitions : ProbeBundle BHist} :
    BundleLocalTrivPackage base total projection fiber trivs transitions ledger ->
      UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fiber ∧
        UnaryHistory ledger ∧ BundleRowsUnary trivs ∧ BundleRowsUnary transitions := by
  intro package
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro package.right.right.left
        (And.intro package.right.right.right.left
          (And.intro package.right.right.right.right.left
            (And.intro package.right.right.right.right.right.left
              package.right.right.right.right.right.right)))))

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

end BEDC.Derived.BundleUp
