import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactRegSeqRatClusterHandoff [AskSetup] [PackageSetup]
    {K B S W R E H C P N clusterRead handoffRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      Cont W R clusterRead →
        Cont clusterRead E handoffRead →
          Cont handoffRead N namedRead →
            PkgSig bundle namedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row N ∨
                      hsame row clusterRead ∨ hsame row handoffRead ∨
                        hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W R clusterRead ∧
                      Cont clusterRead E handoffRead ∧ Cont handoffRead N namedRead ∧
                        PkgSig bundle namedRead pkg)
                  hsame ∧ UnaryHistory clusterRead ∧ UnaryHistory handoffRead ∧
                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier clusterRoute handoffRoute namedRoute namedPkg
  obtain ⟨_kUnary, _bUnary, _sUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, _provenancePkg⟩ := carrier
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed wUnary rUnary clusterRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed clusterUnary eUnary handoffRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed handoffUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row N ∨
              hsame row clusterRead ∨ hsame row handoffRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R clusterRead ∧ Cont clusterRead E handoffRead ∧
              Cont handoffRead N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead
        ⟨hsame_refl namedRead, namedUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, clusterRoute, handoffRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, clusterUnary, handoffUnary, namedUnary⟩

end BEDC.Derived.SequentialCompactUp
