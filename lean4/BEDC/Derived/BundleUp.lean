import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BundleUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

structure BundleLocalTrivPkg (package : BHist) : Type where
  base : BHist
  total : BHist
  projection : BHist
  fibre : BHist
  transition : BHist
  ledger : BHist
  charts : ProbeBundle BHist
  projection_row : hsame projection (append base total)
  package_row : hsame package (append projection fibre)
  transition_row : hsame package (append transition ledger)
  package_unary : UnaryHistory package

def BundleLocalTrivCarrier (package : BHist) : Prop :=
  Nonempty (BundleLocalTrivPkg package)

theorem BundleLocalTrivPkg_trivialization_transition_stability {package package' : BHist} :
    BundleLocalTrivCarrier package → hsame package package' →
      ∃ base total projection fibre transition ledger : BHist,
        ∃ _charts : ProbeBundle BHist,
          BundleLocalTrivCarrier package' ∧ hsame projection (append base total) ∧
            hsame package' (append projection fibre) ∧
              hsame package' (append transition ledger) ∧ UnaryHistory package' := by
  intro carrier samePackage
  cases carrier with
  | intro pkg =>
      have packageProjection : hsame package' (append pkg.projection pkg.fibre) :=
        hsame_trans (hsame_symm samePackage) pkg.package_row
      have packageTransition : hsame package' (append pkg.transition pkg.ledger) :=
        hsame_trans (hsame_symm samePackage) pkg.transition_row
      have packageUnary : UnaryHistory package' :=
        unary_transport pkg.package_unary samePackage
      exact ⟨pkg.base, pkg.total, pkg.projection, pkg.fibre, pkg.transition, pkg.ledger,
        pkg.charts, ⟨Nonempty.intro {
          base := pkg.base
          total := pkg.total
          projection := pkg.projection
          fibre := pkg.fibre
          transition := pkg.transition
          ledger := pkg.ledger
          charts := pkg.charts
          projection_row := pkg.projection_row
          package_row := packageProjection
          transition_row := packageTransition
          package_unary := packageUnary
        }, pkg.projection_row, packageProjection, packageTransition, packageUnary⟩⟩

def BundleLocalTrivTransitionPkg
    (base total projection fibre transition ledger : BHist) (trivs : ProbeBundle BHist) :
    Prop :=
  UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fibre ∧
    UnaryHistory transition ∧ UnaryHistory ledger ∧ Cont base projection total ∧
      Cont total fibre transition ∧ InBundle transition trivs

theorem BundleLocalTrivPkg_transition_stability
    {base total projection fibre transition ledger base' total' projection' fibre' transition'
      ledger' : BHist}
    {trivs : ProbeBundle BHist} :
    BundleLocalTrivTransitionPkg base total projection fibre transition ledger trivs ->
      hsame base base' -> hsame total total' -> hsame projection projection' ->
        hsame fibre fibre' -> hsame transition transition' -> hsame ledger ledger' ->
          BundleLocalTrivTransitionPkg base' total' projection' fibre' transition' ledger' trivs ∧
            hsame transition transition' ∧ UnaryHistory transition' ∧
              InBundle transition' trivs := by
  intro pkg sameBase sameTotal sameProjection sameFibre sameTransition sameLedger
  cases sameBase
  cases sameTotal
  cases sameProjection
  cases sameFibre
  cases sameTransition
  cases sameLedger
  exact And.intro pkg
    (And.intro (hsame_refl transition)
      (And.intro pkg.right.right.right.right.left
        pkg.right.right.right.right.right.right.right.right))

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

def BundleLocalTrivPkgRows (base total projection fibre ledger : BHist)
    (triv transitions : ProbeBundle BHist) : ProbeBundle BHist :=
  ProbeBundle.Bcons base
    (ProbeBundle.Bcons total
      (ProbeBundle.Bcons projection
        (ProbeBundle.Bcons fibre
          (bundleAppend triv (ProbeBundle.Bcons ledger transitions)))))

theorem BundleLocalTrivPkg_projection_rows {base total projection fibre ledger row : BHist}
    {triv transitions : ProbeBundle BHist} :
    InBundle row (BundleLocalTrivPkgRows base total projection fibre ledger triv transitions) ->
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
