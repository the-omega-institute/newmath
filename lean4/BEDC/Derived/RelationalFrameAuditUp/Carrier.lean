import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RelationalFrameAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RelationalFrameAuditCarrier [AskSetup] [PackageSetup]
    (multiHist observerA observerB request symmetry causal rate refusal transport continuation
      provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  UnaryHistory multiHist ∧ UnaryHistory observerA ∧ UnaryHistory observerB ∧
    UnaryHistory request ∧ UnaryHistory symmetry ∧ UnaryHistory causal ∧
      UnaryHistory rate ∧ UnaryHistory refusal ∧ UnaryHistory transport ∧
        UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont multiHist request observerA ∧ Cont request observerB causal ∧
            Cont causal symmetry rate ∧ Cont transport continuation provenance ∧
              PkgSig bundle provenance pkg ∧
                SemanticNameCert
                  (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                  (fun row : BHist => hsame row provenance)
                  (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
                  hsame

theorem RelationalFrameAuditCarrier_observer_symmetry_factorization [AskSetup]
    [PackageSetup]
    {multiHist observerA observerB request symmetry causal rate refusal transport continuation
      provenance name comparison : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RelationalFrameAuditCarrier multiHist observerA observerB request symmetry causal rate
        refusal transport continuation provenance name bundle pkg ->
      Cont observerA observerB causal ->
        Cont causal rate comparison ->
          Cont comparison symmetry continuation ->
            PkgSig bundle comparison pkg ->
              UnaryHistory observerA ∧ UnaryHistory observerB ∧ UnaryHistory causal ∧
                UnaryHistory rate ∧ UnaryHistory comparison ∧
                  Cont observerA observerB causal ∧ Cont causal rate comparison ∧
                    Cont comparison symmetry continuation ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle comparison pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier observerRoute rateRoute symmetryRoute comparisonPkg
  obtain ⟨_multiHistUnary, observerAUnary, observerBUnary, _requestUnary, symmetryUnary,
    causalUnary, rateUnary, _refusalUnary, _transportUnary, _continuationUnary,
    _provenanceUnary, _nameUnary, _multiHistRoute, _requestRoute, _carrierRateRoute,
    _provenanceRoute, provenancePkg, _semanticCert⟩ := carrier
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed causalUnary rateUnary rateRoute
  exact
    ⟨observerAUnary,
      observerBUnary,
      causalUnary,
      rateUnary,
      comparisonUnary,
      observerRoute,
      rateRoute,
      symmetryRoute,
      provenancePkg,
      comparisonPkg⟩

def RelationalFrameAuditLayeredRelationCarrier [AskSetup] [PackageSetup]
    (sourceA sourceB layerMap preserved refused ledger exactness boundary transport continuation
      provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory layerMap ∧
    UnaryHistory preserved ∧ UnaryHistory refused ∧ UnaryHistory ledger ∧
      UnaryHistory exactness ∧ UnaryHistory boundary ∧ UnaryHistory transport ∧
        UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont sourceA layerMap preserved ∧ Cont sourceB layerMap refused ∧
            Cont preserved refused exactness ∧ Cont transport continuation provenance ∧
              PkgSig bundle provenance pkg

theorem RelationalFrameAuditLayeredRelationCert_namecert_obligation_surface [AskSetup]
    [PackageSetup]
    {sourceA sourceB layerMap preserved refused ledger exactness boundary transport
      continuation provenance name handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RelationalFrameAuditLayeredRelationCarrier sourceA sourceB layerMap preserved refused
        ledger exactness boundary transport continuation provenance name bundle pkg ->
      Cont sourceA layerMap preserved ->
        Cont sourceB layerMap refused ->
          Cont preserved refused exactness ->
            Cont exactness boundary handoff ->
              PkgSig bundle handoff pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sourceA ∨ hsame row sourceB ∨ hsame row layerMap ∨
                        hsame row preserved ∨ hsame row refused ∨ hsame row exactness ∨
                          hsame row handoff)
                    (fun row : BHist => hsame row handoff ∧ PkgSig bundle handoff pkg)
                    hsame ∧
                  UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory layerMap ∧
                    UnaryHistory preserved ∧ UnaryHistory refused ∧ UnaryHistory exactness ∧
                      UnaryHistory handoff := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier _sourceARoute _sourceBRoute _exactnessRoute exactnessBoundaryHandoff
    handoffPkg
  obtain ⟨sourceAUnary, sourceBUnary, layerMapUnary, preservedUnary, refusedUnary,
    _ledgerUnary, exactnessUnary, boundaryUnary, _transportUnary, _continuationUnary,
    _provenanceUnary, _nameUnary, _carrierSourceARoute, _carrierSourceBRoute,
    _carrierExactnessRoute, _provenanceRoute, _provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed exactnessUnary boundaryUnary exactnessBoundaryHandoff
  have sourceAtHandoff : hsame handoff handoff ∧ UnaryHistory handoff :=
    ⟨hsame_refl handoff, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceA ∨ hsame row sourceB ∨ hsame row layerMap ∨
              hsame row preserved ∨ hsame row refused ∨ hsame row exactness ∨
                hsame row handoff)
          (fun row : BHist => hsame row handoff ∧ PkgSig bundle handoff pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff sourceAtHandoff
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
      exact ⟨source.left, handoffPkg⟩
  }
  exact
    ⟨cert, sourceAUnary, sourceBUnary, layerMapUnary, preservedUnary, refusedUnary,
      exactnessUnary, handoffUnary⟩

end BEDC.Derived.RelationalFrameAuditUp
