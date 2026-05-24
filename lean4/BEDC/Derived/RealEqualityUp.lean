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

end BEDC.Derived.RealEqualityUp
