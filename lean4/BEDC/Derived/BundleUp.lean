import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
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

end BEDC.Derived.BundleUp
