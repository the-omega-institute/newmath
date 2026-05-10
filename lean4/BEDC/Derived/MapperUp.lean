import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MapperUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MapperCoverPreimageCarrier [AskSetup] [PackageSetup]
    (cover preimage cluster incidence simplex ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory cover ∧ UnaryHistory preimage ∧ UnaryHistory cluster ∧
    UnaryHistory incidence ∧ Cont cover preimage cluster ∧
      Cont cluster incidence simplex ∧
        Cont cover (append preimage (append cluster incidence)) ledger ∧
          PkgSig bundle ledger pkg

theorem MapperCoverPreimageCarrier_cluster_classifier_stability [AskSetup] [PackageSetup]
    {cover preimage cluster incidence simplex ledger cover' preimage' cluster' incidence'
      simplex' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MapperCoverPreimageCarrier cover preimage cluster incidence simplex ledger bundle pkg ->
      hsame cover cover' -> hsame preimage preimage' -> hsame cluster cluster' ->
        hsame incidence incidence' -> Cont cover' preimage' cluster' ->
          Cont cluster' incidence' simplex' ->
            Cont cover' (append preimage' (append cluster' incidence')) ledger' ->
              PkgSig bundle ledger' pkg ->
                MapperCoverPreimageCarrier cover' preimage' cluster' incidence' simplex'
                    ledger' bundle pkg ∧
                  hsame simplex simplex' ∧ hsame ledger ledger' := by
  intro carrier sameCover samePreimage sameCluster sameIncidence clusterRow'
  intro simplexRow' ledgerRow' pkgSig'
  have coverUnary' : UnaryHistory cover' :=
    unary_transport carrier.left sameCover
  have preimageUnary' : UnaryHistory preimage' :=
    unary_transport carrier.right.left samePreimage
  have clusterUnary' : UnaryHistory cluster' :=
    unary_transport carrier.right.right.left sameCluster
  have incidenceUnary' : UnaryHistory incidence' :=
    unary_transport carrier.right.right.right.left sameIncidence
  have sameSimplex : hsame simplex simplex' :=
    cont_respects_hsame sameCluster sameIncidence
      carrier.right.right.right.right.right.left simplexRow'
  have clusterIncidenceSame :
      hsame (append cluster incidence) (append cluster' incidence') :=
    cont_respects_hsame sameCluster sameIncidence
      (rfl : Cont cluster incidence (append cluster incidence))
      (rfl : Cont cluster' incidence' (append cluster' incidence'))
  have ledgerTailSame :
      hsame (append preimage (append cluster incidence))
        (append preimage' (append cluster' incidence')) :=
    cont_respects_hsame samePreimage clusterIncidenceSame
      (rfl : Cont preimage (append cluster incidence)
        (append preimage (append cluster incidence)))
      (rfl : Cont preimage' (append cluster' incidence')
        (append preimage' (append cluster' incidence')))
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameCover ledgerTailSame
      carrier.right.right.right.right.right.right.left ledgerRow'
  exact
    ⟨⟨coverUnary', preimageUnary', clusterUnary', incidenceUnary',
        clusterRow', simplexRow', ledgerRow', pkgSig'⟩, sameSimplex, sameLedger⟩

end BEDC.Derived.MapperUp
