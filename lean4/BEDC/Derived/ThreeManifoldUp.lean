import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ThreeManifoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ThreeManifoldFiniteCarrier [AskSetup] [PackageSetup]
    (manifold topology decomposition classifier contRows provenance : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory topology ∧ UnaryHistory decomposition ∧
    UnaryHistory classifier ∧ UnaryHistory contRows ∧ UnaryHistory provenance ∧
      Cont manifold topology decomposition ∧ Cont decomposition classifier contRows ∧
        PkgSig probe provenance pkg

private def ThreeManifoldFiniteCarrier_obligation_surface_cert [AskSetup] [PackageSetup]
    {manifold topology decomposition classifier contRows provenance : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier :
      ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
        provenance probe pkg) :
      SemanticNameCert
        (fun row : BHist =>
          ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
            provenance probe pkg ∧ hsame row provenance)
        (fun row : BHist =>
          ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
            provenance probe pkg ∧ hsame row provenance)
        (fun row : BHist =>
          ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
            provenance probe pkg ∧ hsame row provenance)
        hsame := {
  core := {
    carrier_inhabited := Exists.intro provenance
      (And.intro carrier (hsame_refl provenance))
    equiv_refl := by
      intro row _source
      exact hsame_refl row
    equiv_symm := by
      intro row row' sameRows
      exact hsame_symm sameRows
    equiv_trans := by
      intro row row' row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    carrier_respects_equiv := by
      intro row row' sameRows sourceRow
      exact And.intro sourceRow.left
        (hsame_trans (hsame_symm sameRows) sourceRow.right)
  }
  pattern_sound := by
    intro _row sourceRow
    exact sourceRow
  ledger_sound := by
    intro _row sourceRow
    exact sourceRow
}

theorem ThreeManifoldFiniteCarrier_obligation_surface [AskSetup] [PackageSetup]
    {manifold topology decomposition classifier contRows provenance : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows provenance
        probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
              provenance probe pkg ∧ hsame row provenance)
          (fun row : BHist =>
            ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
              provenance probe pkg ∧ hsame row provenance)
          (fun row : BHist =>
            ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
              provenance probe pkg ∧ hsame row provenance)
          hsame ∧
        Cont manifold topology decomposition ∧ Cont decomposition classifier contRows ∧
          PkgSig probe provenance pkg := by
  intro carrier
  exact And.intro (ThreeManifoldFiniteCarrier_obligation_surface_cert carrier)
    (And.intro carrier.right.right.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.right.right.left
        carrier.right.right.right.right.right.right.right.right))

theorem ThreeManifoldFiniteCarrier_jsj_ledger_exactness [AskSetup] [PackageSetup]
    {manifold topology decomposition classifier contRows provenance decomposition' contRows' :
      BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows provenance
        probe pkg ->
      hsame decomposition decomposition' ->
      hsame contRows contRows' ->
      Cont manifold topology decomposition' ->
      Cont decomposition' classifier contRows' ->
        ThreeManifoldFiniteCarrier manifold topology decomposition' classifier contRows'
          provenance probe pkg ∧ hsame contRows contRows' := by
  intro carrier sameDecomposition sameContRows manifoldTopologyRow decompositionClassifierRow
  obtain ⟨manifoldUnary, topologyUnary, decompositionUnary, classifierUnary, contRowsUnary,
    provenanceUnary, _sourceManifoldTopologyRow, _sourceDecompositionClassifierRow,
    packageRow⟩ := carrier
  have decompositionUnary' : UnaryHistory decomposition' :=
    unary_transport decompositionUnary sameDecomposition
  have contRowsUnary' : UnaryHistory contRows' :=
    unary_transport contRowsUnary sameContRows
  have transportedCarrier :
      ThreeManifoldFiniteCarrier manifold topology decomposition' classifier contRows'
          provenance probe pkg :=
    And.intro manifoldUnary
        (And.intro topologyUnary
        (And.intro decompositionUnary'
          (And.intro classifierUnary
            (And.intro contRowsUnary'
              (And.intro provenanceUnary
                (And.intro manifoldTopologyRow
                  (And.intro decompositionClassifierRow packageRow)))))))
  exact And.intro transportedCarrier sameContRows

theorem ThreeManifoldFiniteCarrier_chart_transition_ledger_obligation [AskSetup] [PackageSetup]
    {manifold topology decomposition classifier contRows provenance manifold' topology'
      decomposition' classifier' contRows' provenance' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows provenance
        probe pkg ->
      hsame manifold manifold' ->
      hsame topology topology' ->
      hsame classifier classifier' ->
      hsame provenance provenance' ->
      Cont manifold' topology' decomposition' ->
      Cont decomposition' classifier' contRows' ->
      PkgSig probe provenance' pkg ->
      ThreeManifoldFiniteCarrier manifold' topology' decomposition' classifier' contRows'
          provenance' probe pkg ∧
        hsame decomposition decomposition' ∧ hsame contRows contRows' := by
  intro carrier sameManifold sameTopology sameClassifier sameProvenance
    manifoldTopologyRow decompositionClassifierRow pkgRow
  obtain ⟨manifoldUnary, topologyUnary, decompositionUnary, classifierUnary, contRowsUnary,
    provenanceUnary, oldManifoldTopologyRow, oldDecompositionClassifierRow, _oldPkgRow⟩ :=
    carrier
  have manifoldUnary' : UnaryHistory manifold' :=
    unary_transport manifoldUnary sameManifold
  have topologyUnary' : UnaryHistory topology' :=
    unary_transport topologyUnary sameTopology
  have decompositionUnary' : UnaryHistory decomposition' :=
    unary_cont_closed manifoldUnary' topologyUnary' manifoldTopologyRow
  have classifierUnary' : UnaryHistory classifier' :=
    unary_transport classifierUnary sameClassifier
  have contRowsUnary' : UnaryHistory contRows' :=
    unary_cont_closed decompositionUnary' classifierUnary' decompositionClassifierRow
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have sameDecomposition : hsame decomposition decomposition' :=
    cont_respects_hsame sameManifold sameTopology oldManifoldTopologyRow manifoldTopologyRow
  have sameContRows : hsame contRows contRows' :=
    cont_respects_hsame sameDecomposition sameClassifier oldDecompositionClassifierRow
      decompositionClassifierRow
  exact And.intro
    (And.intro manifoldUnary'
      (And.intro topologyUnary'
        (And.intro decompositionUnary'
          (And.intro classifierUnary'
            (And.intro contRowsUnary'
              (And.intro provenanceUnary'
                (And.intro manifoldTopologyRow
                  (And.intro decompositionClassifierRow pkgRow))))))))
    (And.intro sameDecomposition sameContRows)

theorem ThreeManifoldFiniteCarrier_topology_source_scope [AskSetup] [PackageSetup]
    {manifold topology decomposition classifier contRows provenance topology' decomposition'
      contRows' : BHist} {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows provenance
        probe pkg ->
      hsame topology topology' ->
        hsame decomposition decomposition' ->
          Cont manifold topology' decomposition' ->
            Cont decomposition' classifier contRows' ->
              ThreeManifoldFiniteCarrier manifold topology' decomposition' classifier contRows'
                  provenance probe pkg ∧
                hsame contRows contRows' ∧ PkgSig probe provenance pkg := by
  intro carrier sameTopology sameDecomposition manifoldTopologyRow decompositionClassifierRow
  obtain ⟨manifoldUnary, topologyUnary, decompositionUnary, classifierUnary, contRowsUnary,
    provenanceUnary, _manifoldTopologySource, decompositionClassifierSource, pkgSig⟩ := carrier
  have topologyUnary' : UnaryHistory topology' :=
    unary_transport topologyUnary sameTopology
  have decompositionUnary' : UnaryHistory decomposition' :=
    unary_transport decompositionUnary sameDecomposition
  have contRowsSame : hsame contRows contRows' :=
    cont_respects_hsame sameDecomposition (hsame_refl classifier)
      decompositionClassifierSource decompositionClassifierRow
  have contRowsUnary' : UnaryHistory contRows' :=
    unary_transport contRowsUnary contRowsSame
  exact And.intro
    (And.intro manifoldUnary
      (And.intro topologyUnary'
        (And.intro decompositionUnary'
          (And.intro classifierUnary
            (And.intro contRowsUnary'
              (And.intro provenanceUnary
                (And.intro manifoldTopologyRow
                  (And.intro decompositionClassifierRow pkgSig))))))))
    (And.intro contRowsSame pkgSig)

end BEDC.Derived.ThreeManifoldUp
