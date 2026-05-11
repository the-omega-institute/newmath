import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TopVecSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TopVecSpaceBHistCarrier [AskSetup] [PackageSetup]
    (vec topology addLedger scalarLedger route endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory vec ∧ UnaryHistory topology ∧ UnaryHistory addLedger ∧
    UnaryHistory scalarLedger ∧ UnaryHistory route ∧ UnaryHistory endpoint ∧
      Cont vec topology addLedger ∧ Cont addLedger scalarLedger route ∧
        Cont route topology endpoint ∧ PkgSig bundle endpoint pkg

theorem TopVecSpaceBHistCarrier_vecspace_source_obligation [AskSetup] [PackageSetup]
    {vec topology addLedger scalarLedger route endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TopVecSpaceBHistCarrier vec topology addLedger scalarLedger route endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row vec)
          (fun row : BHist => hsame row vec) (fun row : BHist => hsame row vec) hsame ∧
        UnaryHistory vec ∧ Cont vec topology addLedger ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have cert :
      SemanticNameCert (fun row : BHist => hsame row vec)
        (fun row : BHist => hsame row vec) (fun row : BHist => hsame row vec) hsame := {
    core := {
      carrier_inhabited := Exists.intro vec (hsame_refl vec)
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        exact hsame_trans (hsame_symm sameRows) carrierRow
    }
    pattern_sound := by
      intro _row carrierRow
      exact carrierRow
    ledger_sound := by
      intro _row carrierRow
      exact carrierRow
  }
  exact And.intro cert
    (And.intro carrier.left
      (And.intro carrier.right.right.right.right.right.right.left
        carrier.right.right.right.right.right.right.right.right.right))

theorem TopVecSpaceBHistCarrier_continuous_addition_obligation [AskSetup] [PackageSetup]
    {vec topology addLedger scalarLedger route endpoint vec' topology' addLedger'
      scalarLedger' route' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TopVecSpaceBHistCarrier vec topology addLedger scalarLedger route endpoint bundle pkg ->
      hsame vec vec' ->
        hsame topology topology' ->
          hsame scalarLedger scalarLedger' ->
            Cont vec' topology' addLedger' ->
              Cont addLedger' scalarLedger' route' ->
                Cont route' topology' endpoint' ->
                  PkgSig bundle endpoint' pkg ->
                    TopVecSpaceBHistCarrier vec' topology' addLedger' scalarLedger' route'
                        endpoint' bundle pkg ∧
                      hsame addLedger addLedger' ∧ hsame route route' ∧
                        hsame endpoint endpoint' := by
  intro carrier sameVec sameTopology sameScalarLedger addLedgerRow' routeRow' endpointRow'
    pkgSig'
  have vecUnary' : UnaryHistory vec' :=
    unary_transport carrier.left sameVec
  have topologyUnary' : UnaryHistory topology' :=
    unary_transport carrier.right.left sameTopology
  have scalarLedgerUnary' : UnaryHistory scalarLedger' :=
    unary_transport carrier.right.right.right.left sameScalarLedger
  have sameAddLedger : hsame addLedger addLedger' :=
    cont_respects_hsame sameVec sameTopology
      carrier.right.right.right.right.right.right.left addLedgerRow'
  have addLedgerUnary' : UnaryHistory addLedger' :=
    unary_cont_closed vecUnary' topologyUnary' addLedgerRow'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameAddLedger sameScalarLedger
      carrier.right.right.right.right.right.right.right.left routeRow'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed addLedgerUnary' scalarLedgerUnary' routeRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRoute sameTopology
      carrier.right.right.right.right.right.right.right.right.left endpointRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed routeUnary' topologyUnary' endpointRow'
  exact
    And.intro
      (And.intro vecUnary'
        (And.intro topologyUnary'
          (And.intro addLedgerUnary'
            (And.intro scalarLedgerUnary'
              (And.intro routeUnary'
                (And.intro endpointUnary'
                  (And.intro addLedgerRow'
                    (And.intro routeRow' (And.intro endpointRow' pkgSig')))))))))
      (And.intro sameAddLedger (And.intro sameRoute sameEndpoint))

end BEDC.Derived.TopVecSpaceUp
