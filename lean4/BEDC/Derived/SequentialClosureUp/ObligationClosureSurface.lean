import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureObligationClosureSurface [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N surfaceRead replayRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg →
      Cont U W surfaceRead →
        Cont surfaceRead R replayRead →
          Cont replayRead N named →
            PkgSig bundle named pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row named ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨
                      hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row R ∨
                        hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row named)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont U W surfaceRead ∧
                      Cont surfaceRead R replayRead ∧ Cont replayRead N named ∧
                        PkgSig bundle named pkg)
                  hsame ∧ UnaryHistory surfaceRead ∧ UnaryHistory replayRead ∧
                UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier surfaceRoute replayRoute namedRoute namedPkg
  obtain ⟨_topologyUnary, _metricUnary, _sourceUnary, _sequenceUnary, _limitUnary,
    testUnary, windowUnary, rationalUnary, _realUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, nameUnary, _provenancePkg, _namePkg⟩ :=
    carrier
  have surfaceUnary : UnaryHistory surfaceRead :=
    unary_cont_closed testUnary windowUnary surfaceRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed surfaceUnary rationalUnary replayRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed replayUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨
              hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row R ∨
                hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U W surfaceRead ∧
              Cont surfaceRead R replayRead ∧ Cont replayRead N named ∧
                PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, surfaceRoute, replayRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, surfaceUnary, replayUnary, namedUnary⟩

end BEDC.Derived.SequentialClosureUp
