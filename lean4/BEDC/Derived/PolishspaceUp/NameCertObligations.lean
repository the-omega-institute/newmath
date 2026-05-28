import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceNamecertObligations [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport route provenance localName
      membershipRead completionRead denseRead observationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory complete →
        UnaryHistory separable →
          UnaryHistory stream →
            UnaryHistory readback →
              UnaryHistory ledger →
                UnaryHistory transport →
                  Cont metric stream membershipRead →
                    Cont complete stream completionRead →
                      Cont separable stream denseRead →
                        Cont ledger transport route →
                          Cont route readback observationRead →
                            PkgSig bundle provenance pkg →
                              PkgSig bundle localName pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row observationRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row metric ∨ hsame row complete ∨
                                        hsame row separable ∨ hsame row stream ∨
                                          hsame row readback ∨ hsame row ledger ∨
                                            hsame row observationRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg)
                                    hsame ∧
                                  UnaryHistory membershipRead ∧
                                    UnaryHistory completionRead ∧
                                      UnaryHistory denseRead ∧
                                        UnaryHistory observationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro metricUnary completeUnary separableUnary streamUnary readbackUnary ledgerUnary
    transportUnary metricStreamMembership completeStreamCompletion separableStreamDense
    ledgerTransportRoute routeReadbackObservation provenancePkg localNamePkg
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed metricUnary streamUnary metricStreamMembership
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed completeUnary streamUnary completeStreamCompletion
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed separableUnary streamUnary separableStreamDense
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportRoute
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed routeUnary readbackUnary routeReadbackObservation
  have sourceObservation :
      (fun row : BHist => hsame row observationRead ∧ UnaryHistory row) observationRead := by
    exact ⟨hsame_refl observationRead, observationUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row observationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row observationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro observationRead sourceObservation
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
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, membershipUnary, completionUnary, denseUnary, observationUnary⟩

theorem PolishSpaceCompletionDensityObligation [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      completionRead denseRead densityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory complete →
        UnaryHistory separable →
          UnaryHistory stream →
            UnaryHistory readback →
              UnaryHistory ledger →
                UnaryHistory transport →
                  Cont complete stream completionRead →
                    Cont separable stream denseRead →
                      Cont ledger transport replay →
                        Cont replay readback densityRead →
                          PkgSig bundle provenance pkg →
                            PkgSig bundle localName pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row metric ∨ hsame row complete ∨
                                      hsame row separable ∨ hsame row stream ∨
                                        hsame row readback ∨ hsame row ledger ∨
                                          hsame row densityRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory completionRead ∧
                                  UnaryHistory denseRead ∧ UnaryHistory densityRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _metricUnary completeUnary separableUnary streamUnary readbackUnary ledgerUnary
    transportUnary completeStreamCompletion separableStreamDense ledgerTransportReplay
    replayReadbackDensity provenancePkg localNamePkg
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed completeUnary streamUnary completeStreamCompletion
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed separableUnary streamUnary separableStreamDense
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportReplay
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed replayUnary readbackUnary replayReadbackDensity
  have sourceDensity :
      (fun row : BHist => hsame row densityRead ∧ UnaryHistory row) densityRead := by
    exact ⟨hsame_refl densityRead, densityUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row densityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro densityRead sourceDensity
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
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, completionUnary, denseUnary, densityUnary⟩

theorem PolishSpaceRootUnblockCommonMetric [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      completionRead denseRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory complete →
        UnaryHistory separable →
          UnaryHistory stream →
            UnaryHistory readback →
              UnaryHistory ledger →
                UnaryHistory transport →
                  Cont metric complete completionRead →
                    Cont metric separable denseRead →
                      Cont ledger transport replay →
                        Cont replay readback rootRead →
                          PkgSig bundle provenance pkg →
                            PkgSig bundle localName pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row metric ∨ hsame row complete ∨
                                      hsame row separable ∨ hsame row stream ∨
                                        hsame row readback ∨ hsame row ledger ∨
                                          hsame row rootRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory completionRead ∧
                                  UnaryHistory denseRead ∧ UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro metricUnary completeUnary separableUnary _streamUnary readbackUnary ledgerUnary
    transportUnary metricCompleteRead metricSeparableRead ledgerTransportReplay
    replayReadbackRoot provenancePkg localNamePkg
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricCompleteRead
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed metricUnary separableUnary metricSeparableRead
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportReplay
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed replayUnary readbackUnary replayReadbackRoot
  have sourceRoot :
      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row) rootRead := by
    exact ⟨hsame_refl rootRead, rootUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨ hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead sourceRoot
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
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, completionUnary, denseUnary, rootUnary⟩

theorem PolishspaceRootDensityObligations [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport route provenance localName
      denseRead observationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory complete →
        UnaryHistory separable →
          UnaryHistory stream →
            UnaryHistory readback →
              UnaryHistory ledger →
                UnaryHistory transport →
                  Cont separable stream denseRead →
                    Cont ledger transport route →
                      Cont route readback observationRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row observationRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row separable ∨ hsame row stream ∨
                                    hsame row readback ∨ hsame row ledger ∨
                                      hsame row observationRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory denseRead ∧ UnaryHistory observationRead ∧
                                Cont separable stream denseRead ∧
                                  Cont route readback observationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _metricUnary _completeUnary separableUnary streamUnary readbackUnary ledgerUnary
    transportUnary separableStreamDense ledgerTransportRoute routeReadbackObservation
    provenancePkg localNamePkg
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed separableUnary streamUnary separableStreamDense
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportRoute
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed routeUnary readbackUnary routeReadbackObservation
  have sourceObservation :
      (fun row : BHist => hsame row observationRead ∧ UnaryHistory row) observationRead := by
    exact ⟨hsame_refl observationRead, observationUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row observationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row separable ∨ hsame row stream ∨ hsame row readback ∨
              hsame row ledger ∨ hsame row observationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro observationRead sourceObservation
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, denseUnary, observationUnary, separableStreamDense, routeReadbackObservation⟩

end BEDC.Derived.PolishspaceUp
