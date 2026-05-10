import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MapperUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem MapperCoverPreimageCarrier_simplicial_ledger_exactness [AskSetup] [PackageSetup]
    {cover preimage cluster incidence skeleton provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory cover -> UnaryHistory preimage -> UnaryHistory incidence ->
      UnaryHistory provenance -> Cont cover preimage cluster ->
        Cont cluster incidence skeleton -> Cont provenance skeleton endpoint ->
          PkgSig bundle endpoint pkg ->
            UnaryHistory cluster ∧ UnaryHistory skeleton ∧ UnaryHistory endpoint ∧
              hsame cluster (append cover preimage) ∧
                hsame skeleton (append cluster incidence) ∧
                  hsame endpoint (append provenance skeleton) ∧ PkgSig bundle endpoint pkg := by
  intro coverUnary preimageUnary incidenceUnary provenanceUnary clusterRow skeletonRow endpointRow
    pkgSig
  have clusterUnary : UnaryHistory cluster :=
    unary_cont_closed coverUnary preimageUnary clusterRow
  have skeletonUnary : UnaryHistory skeleton :=
    unary_cont_closed clusterUnary incidenceUnary skeletonRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary skeletonUnary endpointRow
  exact
    ⟨clusterUnary, skeletonUnary, endpointUnary, clusterRow, skeletonRow, endpointRow, pkgSig⟩

theorem MapperCoverPreimageCarrier_topology_boundary_exclusions [AskSetup] [PackageSetup]
    {cover preimage cluster incidence simplex ledger consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MapperCoverPreimageCarrier cover preimage cluster incidence simplex ledger bundle pkg ->
      Cont simplex ledger consumer ->
        UnaryHistory consumer ∧ hsame consumer (append simplex ledger) ∧
          hsame simplex (append cluster incidence) ∧
            hsame ledger (append cover (append preimage (append cluster incidence))) ∧
              PkgSig bundle ledger pkg := by
  intro carrier consumerCont
  have clusterIncidenceUnary : UnaryHistory (append cluster incidence) :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      (rfl : Cont cluster incidence (append cluster incidence))
  have preimageClusterIncidenceUnary :
      UnaryHistory (append preimage (append cluster incidence)) :=
    unary_cont_closed carrier.right.left clusterIncidenceUnary
      (rfl : Cont preimage (append cluster incidence)
        (append preimage (append cluster incidence)))
  have simplexUnary : UnaryHistory simplex :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.left preimageClusterIncidenceUnary
      carrier.right.right.right.right.right.right.left
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed simplexUnary ledgerUnary consumerCont
  exact
    ⟨consumerUnary, consumerCont, carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right⟩

theorem MapperCoverPreimageCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {cover preimage cluster incidence simplex ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MapperCoverPreimageCarrier cover preimage cluster incidence simplex ledger bundle pkg ->
      SemanticNameCert
        (fun h : BHist =>
          exists l : BHist,
            MapperCoverPreimageCarrier cover preimage cluster incidence simplex l bundle pkg ∧
              hsame h l)
        (fun h : BHist =>
          exists l : BHist,
            MapperCoverPreimageCarrier cover preimage cluster incidence simplex l bundle pkg ∧
              hsame h l)
        (fun h : BHist =>
          exists l : BHist,
            MapperCoverPreimageCarrier cover preimage cluster incidence simplex l bundle pkg ∧
              hsame h l)
        (fun h k : BHist =>
          (exists l : BHist,
            MapperCoverPreimageCarrier cover preimage cluster incidence simplex l bundle pkg ∧
              hsame h l) ∧
            (exists r : BHist,
              MapperCoverPreimageCarrier cover preimage cluster incidence simplex r bundle pkg ∧
                hsame k r) ∧
              hsame h k) := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro ledger (Exists.intro ledger (And.intro carrier (hsame_refl ledger)))
      equiv_refl := by
        intro h sourceH
        exact And.intro sourceH (And.intro sourceH (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro _h _k classified _sourceH
        exact classified.right.left
    }
    pattern_sound := by
      intro _h sourceH
      exact sourceH
    ledger_sound := by
      intro _h sourceH
      exact sourceH
  }

end BEDC.Derived.MapperUp
