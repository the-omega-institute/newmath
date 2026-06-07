import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactClusterCarrierStability [AskSetup] [PackageSetup]
    {compact baire stream window regular realSeal transport replay provenance localName
      clusterRead transportedCluster sealedCluster : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier compact baire stream window regular realSeal transport replay
        provenance localName bundle pkg ->
      Cont window regular clusterRead ->
        hsame transportedCluster clusterRead ->
          Cont transportedCluster realSeal sealedCluster ->
            PkgSig bundle sealedCluster pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealedCluster ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row window ∨ hsame row regular ∨ hsame row realSeal ∨
                      hsame row sealedCluster)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont window regular clusterRead ∧
                      Cont transportedCluster realSeal sealedCluster ∧
                        PkgSig bundle sealedCluster pkg)
                  hsame ∧ UnaryHistory clusterRead ∧ UnaryHistory transportedCluster ∧
                UnaryHistory sealedCluster := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier clusterRoute transportedSame sealedRoute sealedPkg
  obtain ⟨_compactUnary, _baireUnary, _streamUnary, windowUnary, regularUnary,
    realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, _provenancePkg⟩ := carrier
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed windowUnary regularUnary clusterRoute
  have transportedUnary : UnaryHistory transportedCluster :=
    unary_transport clusterUnary (hsame_symm transportedSame)
  have sealedUnary : UnaryHistory sealedCluster :=
    unary_cont_closed transportedUnary realSealUnary sealedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedCluster ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row regular ∨ hsame row realSeal ∨
              hsame row sealedCluster)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont window regular clusterRead ∧
              Cont transportedCluster realSeal sealedCluster ∧ PkgSig bundle sealedCluster pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedCluster
        ⟨hsame_refl sealedCluster, sealedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, clusterRoute, sealedRoute, sealedPkg⟩
  }
  exact ⟨cert, clusterUnary, transportedUnary, sealedUnary⟩

end BEDC.Derived.SequentialCompactUp
