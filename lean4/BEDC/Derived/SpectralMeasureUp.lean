import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpectralMeasureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SpectralMeasureFiniteAdditivityLedger [AskSetup] [PackageSetup]
    (event projection other union orthogonality additivity : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory event ∧ UnaryHistory projection ∧ UnaryHistory other ∧
    UnaryHistory orthogonality ∧ Cont projection other union ∧
      Cont union orthogonality additivity ∧ PkgSig bundle additivity pkg

theorem SpectralMeasureOrthogonalFiniteAdditivity_row [AskSetup] [PackageSetup]
    {event projection other union orthogonality additivity event' projection' other' union'
      orthogonality' additivity' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralMeasureFiniteAdditivityLedger event projection other union orthogonality additivity
        bundle pkg ->
      hsame event event' -> hsame projection projection' -> hsame other other' ->
        hsame orthogonality orthogonality' -> Cont projection' other' union' ->
          Cont union' orthogonality' additivity' -> PkgSig bundle additivity' pkg ->
            SpectralMeasureFiniteAdditivityLedger event' projection' other' union'
                orthogonality' additivity' bundle pkg ∧
              hsame union union' ∧ hsame additivity additivity' := by
  intro ledger sameEvent sameProjection sameOther sameOrthogonality unionRow' additivityRow'
    pkgSig'
  have eventUnary' : UnaryHistory event' :=
    unary_transport ledger.left sameEvent
  have projectionUnary' : UnaryHistory projection' :=
    unary_transport ledger.right.left sameProjection
  have otherUnary' : UnaryHistory other' :=
    unary_transport ledger.right.right.left sameOther
  have orthogonalityUnary' : UnaryHistory orthogonality' :=
    unary_transport ledger.right.right.right.left sameOrthogonality
  have sameUnion : hsame union union' :=
    cont_respects_hsame sameProjection sameOther ledger.right.right.right.right.left unionRow'
  have unionUnary' : UnaryHistory union' :=
    unary_cont_closed projectionUnary' otherUnary' unionRow'
  have sameAdditivity : hsame additivity additivity' :=
    cont_respects_hsame sameUnion sameOrthogonality ledger.right.right.right.right.right.left
      additivityRow'
  exact
    And.intro
      (And.intro eventUnary'
        (And.intro projectionUnary'
          (And.intro otherUnary'
            (And.intro orthogonalityUnary'
              (And.intro unionRow'
                (And.intro additivityRow' pkgSig'))))))
      (And.intro sameUnion sameAdditivity)

end BEDC.Derived.SpectralMeasureUp
