import BEDC.Derived.RealSequenceLimitUp

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitDiagonalWindowUniqueness [AskSetup] [PackageSetup]
    {sequence limit window dyadic classifier transport replay provenance name diagonalRead
      diagonalSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RealSequenceLimitUp sequence limit window dyadic classifier transport replay
        provenance name bundle pkg →
      Cont window dyadic diagonalRead →
        Cont diagonalRead classifier diagonalSeal →
          PkgSig bundle diagonalSeal pkg →
            UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory diagonalRead ∧
              UnaryHistory diagonalSeal ∧ Cont window dyadic diagonalRead ∧
                Cont diagonalRead classifier diagonalSeal ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle diagonalSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier windowDyadicRead readClassifierSeal sealPkg
  obtain ⟨_sequenceUnary, _limitUnary, windowUnary, dyadicUnary, classifierUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _sequenceWindowReplay,
    _limitDyadicClassifier, _transportSame, _replaySame, _provenancePkg, namePkg⟩ := carrier
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicRead
  have diagonalSealUnary : UnaryHistory diagonalSeal :=
    unary_cont_closed diagonalReadUnary classifierUnary readClassifierSeal
  exact
    ⟨windowUnary, dyadicUnary, diagonalReadUnary, diagonalSealUnary, windowDyadicRead,
      readClassifierSeal, namePkg, sealPkg⟩

end BEDC.Derived.RealSequenceLimitUp
