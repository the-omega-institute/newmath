import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegSeqRatCommonTailWindowPacket [AskSetup] [PackageSetup]
    (source tail0 tail1 commonWindow endpoint radius regularity classifier0 classifier1
      classifierCommon realSeal transport route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  RegSeqRatStreamCarrier source tail0 endpoint radius regularity provenance classifier0
      bundle pkg ∧
    RegSeqRatStreamCarrier source tail1 endpoint radius regularity provenance classifier1
      bundle pkg ∧
      RegSeqRatClassifier endpoint radius regularity classifier0 endpoint radius regularity
        classifierCommon ∧
        RegSeqRatClassifier endpoint radius regularity classifier1 endpoint radius regularity
          classifierCommon ∧
          UnaryHistory commonWindow ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
            UnaryHistory route ∧ UnaryHistory cert ∧ hsame classifier0 classifierCommon ∧
              hsame classifier1 classifierCommon ∧ Cont commonWindow realSeal transport ∧
                Cont classifierCommon realSeal route ∧ PkgSig bundle cert pkg

theorem RegSeqRatCommonTailUnionClassifierDeterminacy [AskSetup] [PackageSetup]
    {source tail0 tail1 commonWindow endpoint radius regularity classifier0 classifier1
      classifierCommon realSeal transport route provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatCommonTailWindowPacket source tail0 tail1 commonWindow endpoint radius regularity
        classifier0 classifier1 classifierCommon realSeal transport route provenance cert
        bundle pkg →
      RegSeqRatClassifier endpoint radius regularity classifier1 endpoint radius regularity
          classifierCommon ∧
        UnaryHistory commonWindow ∧ Cont classifierCommon realSeal route ∧
          PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame RegSeqRatClassifier
  intro packet
  rcases packet with
    ⟨carrier0, carrier1, classifierFrom0, classifierFrom1, commonWindowUnary,
      _realSealUnary, _transportUnary, _routeUnary, _certUnary, sameClassifier0,
      sameClassifier1, _commonWindowTransport, classifierSealRoute, certPkg⟩
  rcases classifierFrom0 with
    ⟨endpointUnary, radiusUnary, regularityUnary, classifier0Unary, _endpointUnaryCommon,
      _radiusUnaryCommon, _regularityUnaryCommon, classifierCommonUnary0, sameEndpoint0,
      sameRadius0, sameRegularity0, _sameClassifier0Readback⟩
  have classifierCommonUnary : UnaryHistory classifierCommon :=
    unary_transport classifier0Unary sameClassifier0
  have sameReadback1 : hsame classifier1 classifierCommon := sameClassifier1
  have classifier1Unary : UnaryHistory classifier1 :=
    carrier1.right.right.right.right.right.right.left
  have classifierRead :
      RegSeqRatClassifier endpoint radius regularity classifier1 endpoint radius regularity
          classifierCommon :=
    ⟨endpointUnary, radiusUnary, regularityUnary, classifier1Unary, endpointUnary,
      radiusUnary, regularityUnary, classifierCommonUnary, hsame_refl endpoint,
      hsame_refl radius, hsame_refl regularity, sameReadback1⟩
  have _commonTailDeterminacy : hsame classifier0 classifier1 :=
    hsame_trans sameClassifier0 (hsame_symm sameClassifier1)
  have _sourceClassifierConsistency :
      hsame classifierCommon classifierCommon :=
    hsame_trans (hsame_symm sameClassifier0) sameClassifier0
  have _endpointConsistency : hsame endpoint endpoint :=
    hsame_trans sameEndpoint0 (hsame_symm sameEndpoint0)
  have _radiusConsistency : hsame radius radius :=
    hsame_trans sameRadius0 (hsame_symm sameRadius0)
  have _regularityConsistency : hsame regularity regularity :=
    hsame_trans sameRegularity0 (hsame_symm sameRegularity0)
  exact ⟨classifierRead, commonWindowUnary, classifierSealRoute, certPkg⟩

end BEDC.Derived.RegSeqRatUp
