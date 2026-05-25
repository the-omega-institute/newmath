import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyScalarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyScalarCarrier [AskSetup] [PackageSetup]
    (source scalar window sourceObservation scaledLedger realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory source ∧ UnaryHistory scalar ∧ UnaryHistory window ∧
    UnaryHistory sourceObservation ∧ UnaryHistory scaledLedger ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont window source sourceObservation ∧
          Cont sourceObservation scalar scaledLedger ∧ Cont scaledLedger replay realSeal ∧
            hsame transport (append scaledLedger replay) ∧ PkgSig bundle provenance pkg

theorem RegularCauchyScalarRealHandoff [AskSetup] [PackageSetup]
    {X A W D F E H C P N sourceRead scaledRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScalarCarrier X A W D F E H C P N bundle pkg ->
      Cont X W sourceRead ->
        Cont sourceRead F scaledRead ->
          Cont scaledRead E realRead ->
            PkgSig bundle realRead pkg ->
              UnaryHistory X ∧ UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory F ∧
                UnaryHistory E ∧ UnaryHistory sourceRead ∧ UnaryHistory scaledRead ∧
                  UnaryHistory realRead ∧ Cont X W sourceRead ∧ Cont sourceRead F scaledRead ∧
                    Cont scaledRead E realRead ∧ hsame H (append F C) ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier sourceCont scaledCont realCont realPkg
  rcases carrier with
    ⟨unaryX, unaryA, unaryW, _unaryD, unaryF, unaryE, _unaryH, _unaryC, unaryP,
      _unaryN, _windowSourceObservation, _observationScalarScaled, _scaledReplayReal,
      sameTransport, provenancePkg⟩
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryX unaryW sourceCont
  have scaledReadUnary : UnaryHistory scaledRead :=
    unary_cont_closed sourceReadUnary unaryF scaledCont
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed scaledReadUnary unaryE realCont
  exact
    ⟨unaryX, unaryA, unaryW, unaryF, unaryE, sourceReadUnary, scaledReadUnary,
      realReadUnary, sourceCont, scaledCont, realCont, sameTransport, provenancePkg, realPkg⟩

end BEDC.Derived.RegularCauchyScalarUp
