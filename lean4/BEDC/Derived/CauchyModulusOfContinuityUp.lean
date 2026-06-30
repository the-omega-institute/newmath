import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusOfContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusOfContinuityCarrier [AskSetup] [PackageSetup]
    (source target modulus transformer readback realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory modulus ∧
    UnaryHistory transformer ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        Cont modulus source transformer ∧ Cont transformer target readback ∧
          Cont readback realSeal localName ∧ Cont transport replay provenance ∧
            PkgSig bundle localName pkg

theorem CauchyModulusOfContinuityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source target modulus transformer readback realSeal transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusOfContinuityCarrier source target modulus transformer readback realSeal
        transport replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row modulus ∨
              hsame row transformer ∨ hsame row readback ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus source transformer ∧
              Cont transformer target readback ∧ Cont readback realSeal localName ∧
                PkgSig bundle localName pkg)
          hsame ∧
        UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨_sourceUnary, _targetUnary, _modulusUnary, _transformerUnary, _readbackUnary,
    realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, modulusSourceTransformer,
    transformerTargetReadback, readbackRealSealLocalName, _transportReplayProvenance,
    localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row modulus ∨
              hsame row transformer ∨ hsame row readback ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus source transformer ∧
              Cont transformer target readback ∧ Cont readback realSeal localName ∧
                PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.right, modulusSourceTransformer, transformerTargetReadback,
            readbackRealSealLocalName, localNamePkg⟩
    }
  exact ⟨cert, realSealUnary⟩

theorem CauchyModulusOfContinuityCarrier_cauchy_continuous_map_threshold_handoff
    [AskSetup] [PackageSetup]
    {source target modulus transformer readback realSeal transport replay provenance
      localName targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusOfContinuityCarrier source target modulus transformer readback realSeal
        transport replay provenance localName bundle pkg ->
      Cont modulus source targetRead ->
        PkgSig bundle targetRead pkg ->
          UnaryHistory source ∧ UnaryHistory modulus ∧ UnaryHistory transformer ∧
            UnaryHistory targetRead ∧ Cont modulus source transformer ∧
              Cont modulus source targetRead ∧ Cont transformer target readback ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier targetReadRoute targetReadPkg
  obtain ⟨sourceUnary, _targetUnary, modulusUnary, transformerUnary, _readbackUnary,
    _realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    modulusSourceTransformer, transformerTargetReadback, _readbackRealSealLocalName,
    _transportReplayProvenance, localNamePkg⟩ := carrier
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed modulusUnary sourceUnary targetReadRoute
  exact
    ⟨sourceUnary, modulusUnary, transformerUnary, targetReadUnary,
      modulusSourceTransformer, targetReadRoute, transformerTargetReadback, localNamePkg,
      targetReadPkg⟩

theorem CauchyModulusOfContinuityRealConsumerBoundary [AskSetup] [PackageSetup]
    {source target modulus transformer readback realSeal transport replay provenance localName
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusOfContinuityCarrier source target modulus transformer readback realSeal
        transport replay provenance localName bundle pkg ->
      Cont readback realSeal consumerRead ->
        PkgSig bundle consumerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row target ∨ hsame row modulus ∨
                  hsame row transformer ∨ hsame row readback ∨ hsame row realSeal ∨
                    hsame row consumerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont readback realSeal consumerRead ∧
                  PkgSig bundle consumerRead pkg ∧ PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier consumerRoute consumerPkg
  obtain ⟨_sourceUnary, _targetUnary, _modulusUnary, _transformerUnary, readbackUnary,
    realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _modulusSourceTransformer, _transformerTargetReadback, _readbackRealSealLocalName,
    _transportReplayProvenance, localNamePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed readbackUnary realSealUnary consumerRoute
  have sourceAtConsumer :
      hsame consumerRead consumerRead ∧ UnaryHistory consumerRead :=
    ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row modulus ∨
              hsame row transformer ∨ hsame row readback ∨ hsame row realSeal ∨
                hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont readback realSeal consumerRead ∧
              PkgSig bundle consumerRead pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, consumerRoute, consumerPkg, localNamePkg⟩
  }
  exact ⟨cert, readbackUnary, realSealUnary, consumerUnary⟩

theorem CauchyModulusOfContinuityCarrier_scoped_route [AskSetup] [PackageSetup]
    {source target modulus transformer readback realSeal transport replay provenance localName
      targetRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusOfContinuityCarrier source target modulus transformer readback realSeal
        transport replay provenance localName bundle pkg ->
      Cont modulus source targetRead ->
        Cont readback realSeal consumerRead ->
          PkgSig bundle targetRead pkg ->
            PkgSig bundle consumerRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row targetRead ∨ hsame row consumerRead ∨
                      hsame row modulus ∨ hsame row transformer)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont modulus source targetRead ∧
                      Cont readback realSeal consumerRead ∧ PkgSig bundle consumerRead pkg)
                  hsame ∧
                UnaryHistory source ∧ UnaryHistory targetRead ∧ UnaryHistory consumerRead ∧
                  Cont modulus source transformer ∧ Cont transformer target readback ∧
                    Cont readback realSeal consumerRead ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier targetReadRoute consumerRoute _targetReadPkg consumerPkg
  obtain ⟨sourceUnary, _targetUnary, modulusUnary, _transformerUnary, readbackUnary,
    realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    modulusSourceTransformer, transformerTargetReadback, _readbackRealSealLocalName,
    _transportReplayProvenance, localNamePkg⟩ := carrier
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed modulusUnary sourceUnary targetReadRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed readbackUnary realSealUnary consumerRoute
  have sourceAtConsumer :
      hsame consumerRead consumerRead ∧ UnaryHistory consumerRead :=
    ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row targetRead ∨ hsame row consumerRead ∨
              hsame row modulus ∨ hsame row transformer)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus source targetRead ∧
              Cont readback realSeal consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, targetReadRoute, consumerRoute, consumerPkg⟩
  }
  exact
    ⟨cert, sourceUnary, targetReadUnary, consumerUnary, modulusSourceTransformer,
      transformerTargetReadback, consumerRoute, localNamePkg⟩

theorem CauchyModulusOfContinuityCarrier_window_monotonicity [AskSetup] [PackageSetup]
    {source target targetPlus modulus modulusPlus transformer readback readbackPlus realSeal
      realSealPlus transport transportPlus replay replayPlus provenance provenancePlus localName
      localNamePlus targetRead enlargedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusOfContinuityCarrier source target modulus transformer readback realSeal
        transport replay provenance localName bundle pkg ->
      CauchyModulusOfContinuityCarrier source targetPlus modulusPlus transformer readbackPlus
          realSealPlus transportPlus replayPlus provenancePlus localNamePlus bundle pkg ->
        Cont modulus source targetRead ->
          Cont modulusPlus targetRead enlargedRead ->
            PkgSig bundle enlargedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row enlargedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row targetRead ∨ hsame row enlargedRead ∨
                      hsame row modulusPlus ∨ hsame row transformer)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont modulus source targetRead ∧
                      Cont modulusPlus targetRead enlargedRead ∧
                        PkgSig bundle enlargedRead pkg)
                  hsame ∧
                UnaryHistory targetRead ∧ UnaryHistory enlargedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier carrierPlus targetRoute enlargedRoute enlargedPkg
  obtain ⟨sourceUnary, _targetUnary, modulusUnary, _transformerUnary, _readbackUnary,
    _realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _modulusSourceTransformer, _transformerTargetReadback, _readbackRealSealLocalName,
    _transportReplayProvenance, _localNamePkg⟩ := carrier
  obtain ⟨_sourceUnaryPlus, _targetPlusUnary, modulusPlusUnary, transformerUnary,
    _readbackPlusUnary, _realSealPlusUnary, _transportPlusUnary, _replayPlusUnary,
    _provenancePlusUnary, _modulusPlusSourceTransformer, _transformerTargetPlusReadbackPlus,
    _readbackPlusRealSealPlusLocalNamePlus, _transportPlusReplayPlusProvenancePlus,
    _localNamePlusPkg⟩ := carrierPlus
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed modulusUnary sourceUnary targetRoute
  have enlargedUnary : UnaryHistory enlargedRead :=
    unary_cont_closed modulusPlusUnary targetReadUnary enlargedRoute
  have sourceAtEnlarged :
      hsame enlargedRead enlargedRead ∧ UnaryHistory enlargedRead :=
    ⟨hsame_refl enlargedRead, enlargedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row enlargedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row targetRead ∨ hsame row enlargedRead ∨
              hsame row modulusPlus ∨ hsame row transformer)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus source targetRead ∧
              Cont modulusPlus targetRead enlargedRead ∧ PkgSig bundle enlargedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro enlargedRead sourceAtEnlarged
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, targetRoute, enlargedRoute, enlargedPkg⟩
  }
  exact ⟨cert, targetReadUnary, enlargedUnary⟩

end BEDC.Derived.CauchyModulusOfContinuityUp
