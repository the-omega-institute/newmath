import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealEqualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealEqualityCarrier [AskSetup] [PackageSetup]
    (leftSeal rightSeal leftWindow rightWindow leftRead rightRead sharedWindow tolerance
      uniformity classifier transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftSeal ∧ UnaryHistory rightSeal ∧ UnaryHistory leftWindow ∧
    UnaryHistory rightWindow ∧ UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
      UnaryHistory sharedWindow ∧ UnaryHistory tolerance ∧ UnaryHistory uniformity ∧
        UnaryHistory classifier ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
          UnaryHistory provenance ∧ UnaryHistory localName ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem RealEqualityCarrier_classifier_stability [AskSetup] [PackageSetup]
    {leftSeal rightSeal leftWindow rightWindow leftRead rightRead sharedWindow tolerance
      uniformity classifier transport replay provenance localName refinedWindow
      refinedClassifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealEqualityCarrier leftSeal rightSeal leftWindow rightWindow leftRead rightRead
        sharedWindow tolerance uniformity classifier transport replay provenance localName
        bundle pkg →
      Cont sharedWindow tolerance uniformity →
        Cont refinedWindow tolerance refinedClassifier →
          hsame sharedWindow refinedWindow →
            UnaryHistory refinedWindow ∧ UnaryHistory refinedClassifier ∧
              hsame uniformity refinedClassifier ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sharedToleranceUniformity refinedToleranceClassifier sameWindow
  obtain ⟨_leftSealUnary, _rightSealUnary, _leftWindowUnary, _rightWindowUnary,
    _leftReadUnary, _rightReadUnary, sharedUnary, toleranceUnary, _uniformityUnary,
    _classifierUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have refinedWindowUnary : UnaryHistory refinedWindow :=
    unary_transport sharedUnary sameWindow
  have refinedClassifierUnary : UnaryHistory refinedClassifier :=
    unary_cont_closed refinedWindowUnary toleranceUnary refinedToleranceClassifier
  have sameClassifier : hsame uniformity refinedClassifier :=
    cont_respects_hsame sameWindow (hsame_refl tolerance) sharedToleranceUniformity
      refinedToleranceClassifier
  exact ⟨refinedWindowUnary, refinedClassifierUnary, sameClassifier, provenancePkg⟩

theorem RealEqualityCarrier_namecert_boundary [AskSetup] [PackageSetup]
    {leftSeal rightSeal leftWindow rightWindow leftReadback rightReadback sharedWindow
      toleranceLedger uniformity classifier transport replay provenance localName classifierRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealEqualityCarrier leftSeal rightSeal leftWindow rightWindow leftReadback rightReadback
        sharedWindow toleranceLedger uniformity classifier transport replay provenance localName
        bundle pkg →
      Cont sharedWindow toleranceLedger classifierRead →
        Cont classifierRead uniformity boundaryRead →
          PkgSig bundle boundaryRead pkg →
            UnaryHistory sharedWindow ∧ UnaryHistory toleranceLedger ∧
              UnaryHistory uniformity ∧ UnaryHistory classifierRead ∧
                UnaryHistory boundaryRead ∧ Cont sharedWindow toleranceLedger classifierRead ∧
                  Cont classifierRead uniformity boundaryRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sharedTolerance classifierUniformity boundaryPkg
  obtain ⟨_leftSealUnary, _rightSealUnary, _leftWindowUnary, _rightWindowUnary,
    _leftReadUnary, _rightReadUnary, sharedUnary, toleranceUnary, uniformityUnary,
    _classifierUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed sharedUnary toleranceUnary sharedTolerance
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed classifierReadUnary uniformityUnary classifierUniformity
  exact
    ⟨sharedUnary, toleranceUnary, uniformityUnary, classifierReadUnary, boundaryReadUnary,
      sharedTolerance, classifierUniformity, provenancePkg, boundaryPkg⟩

theorem RealEqualityCarrier_public_boundary [AskSetup] [PackageSetup]
    {leftSeal rightSeal leftWindow rightWindow leftReadback rightReadback sharedWindow
      toleranceLedger uniformity classifier transport replay provenance localName classifierRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealEqualityCarrier leftSeal rightSeal leftWindow rightWindow leftReadback rightReadback
        sharedWindow toleranceLedger uniformity classifier transport replay provenance localName
        bundle pkg →
      Cont sharedWindow toleranceLedger classifierRead →
        Cont classifierRead uniformity boundaryRead →
          PkgSig bundle boundaryRead pkg →
            UnaryHistory leftSeal ∧ UnaryHistory rightSeal ∧ UnaryHistory sharedWindow ∧
              UnaryHistory toleranceLedger ∧ UnaryHistory uniformity ∧
                UnaryHistory classifierRead ∧ UnaryHistory boundaryRead ∧
                  Cont sharedWindow toleranceLedger classifierRead ∧
                    Cont classifierRead uniformity boundaryRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sharedTolerance classifierUniformity boundaryPkg
  obtain ⟨leftSealUnary, rightSealUnary, _leftWindowUnary, _rightWindowUnary,
    _leftReadUnary, _rightReadUnary, sharedUnary, toleranceUnary, uniformityUnary,
    _classifierUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed sharedUnary toleranceUnary sharedTolerance
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed classifierReadUnary uniformityUnary classifierUniformity
  exact
    ⟨leftSealUnary, rightSealUnary, sharedUnary, toleranceUnary, uniformityUnary,
      classifierReadUnary, boundaryReadUnary, sharedTolerance, classifierUniformity,
      provenancePkg, boundaryPkg⟩

theorem RealEqualityCarrier_regseqrat_dependency_route [AskSetup] [PackageSetup]
    {leftSeal rightSeal leftWindow rightWindow leftRead rightRead sharedWindow tolerance
      uniformity classifier transport replay provenance localName streamRoute regseqRoute
      sourceRoute toleranceRoute comparisonRead equalityBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealEqualityCarrier leftSeal rightSeal leftWindow rightWindow leftRead rightRead
        sharedWindow tolerance uniformity classifier transport replay provenance localName
        bundle pkg →
      Cont leftWindow rightWindow streamRoute →
        Cont leftRead rightRead regseqRoute →
          Cont streamRoute regseqRoute sourceRoute →
            Cont sharedWindow tolerance toleranceRoute →
              Cont sourceRoute toleranceRoute comparisonRead →
                Cont comparisonRead uniformity equalityBoundary →
                  PkgSig bundle equalityBoundary pkg →
                    UnaryHistory leftWindow ∧ UnaryHistory rightWindow ∧
                      UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                        UnaryHistory sharedWindow ∧ UnaryHistory tolerance ∧
                          UnaryHistory uniformity ∧ UnaryHistory streamRoute ∧
                            UnaryHistory regseqRoute ∧ UnaryHistory sourceRoute ∧
                              UnaryHistory toleranceRoute ∧ UnaryHistory comparisonRead ∧
                                UnaryHistory equalityBoundary ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle equalityBoundary pkg := by
  -- BEDC touchpoint anchor: RealEqualityCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier streamStep regseqStep sourceStep toleranceStep comparisonStep equalityStep
    equalityPkg
  obtain ⟨_leftSealUnary, _rightSealUnary, leftWindowUnary, rightWindowUnary,
    leftReadUnary, rightReadUnary, sharedWindowUnary, toleranceUnary, uniformityUnary,
    _classifierUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have streamRouteUnary : UnaryHistory streamRoute :=
    unary_cont_closed leftWindowUnary rightWindowUnary streamStep
  have regseqRouteUnary : UnaryHistory regseqRoute :=
    unary_cont_closed leftReadUnary rightReadUnary regseqStep
  have sourceRouteUnary : UnaryHistory sourceRoute :=
    unary_cont_closed streamRouteUnary regseqRouteUnary sourceStep
  have toleranceRouteUnary : UnaryHistory toleranceRoute :=
    unary_cont_closed sharedWindowUnary toleranceUnary toleranceStep
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed sourceRouteUnary toleranceRouteUnary comparisonStep
  have equalityBoundaryUnary : UnaryHistory equalityBoundary :=
    unary_cont_closed comparisonReadUnary uniformityUnary equalityStep
  exact
    ⟨leftWindowUnary, rightWindowUnary, leftReadUnary, rightReadUnary, sharedWindowUnary,
      toleranceUnary, uniformityUnary, streamRouteUnary, regseqRouteUnary, sourceRouteUnary,
      toleranceRouteUnary, comparisonReadUnary, equalityBoundaryUnary, provenancePkg,
      equalityPkg⟩

end BEDC.Derived.RealEqualityUp
