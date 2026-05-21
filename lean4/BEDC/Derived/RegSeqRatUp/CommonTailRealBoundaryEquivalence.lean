import BEDC.Derived.RegSeqRatUp.CommonTailWindow

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatCommonTailRealBoundaryEquivalence [AskSetup] [PackageSetup]
    {source tail0 tail1 commonWindow endpoint radius regularity classifier0 classifier1
      classifierCommon realSeal transport route provenance cert terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatCommonTailWindowPacket source tail0 tail1 commonWindow endpoint radius regularity
        classifier0 classifier1 classifierCommon realSeal transport route provenance cert
        bundle pkg →
      Cont route cert terminalRead →
        PkgSig bundle terminalRead pkg →
          UnaryHistory commonWindow ∧ UnaryHistory realSeal ∧ UnaryHistory route ∧
            UnaryHistory cert ∧ UnaryHistory terminalRead ∧ hsame classifier0 classifierCommon ∧
              hsame classifier1 classifierCommon ∧ Cont commonWindow realSeal transport ∧
                Cont classifierCommon realSeal route ∧ Cont route cert terminalRead ∧
                  PkgSig bundle cert pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro packet terminalRoute terminalPkg
  obtain ⟨_carrier0, _carrier1, _classifierFrom0, _classifierFrom1, commonWindowUnary,
    realSealUnary, _transportUnary, routeUnary, certUnary, sameClassifier0,
    sameClassifier1, commonWindowTransport, classifierSealRoute, certPkg⟩ := packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary certUnary terminalRoute
  exact
    ⟨commonWindowUnary, realSealUnary, routeUnary, certUnary, terminalReadUnary,
      sameClassifier0, sameClassifier1, commonWindowTransport, classifierSealRoute,
      terminalRoute, certPkg, terminalPkg⟩

end BEDC.Derived.RegSeqRatUp
