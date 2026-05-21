import BEDC.Derived.RegularCauchyTailMeetUp

namespace BEDC.Derived.RegularCauchyTailMeetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailMeetPacket_shared_threshold_cofinality [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n tau' q' l' realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg →
      hsame tau tau' →
        hsame q q' →
          Cont tau' q' l' →
            Cont l' n realSeal →
              PkgSig bundle l' pkg →
                PkgSig bundle realSeal pkg →
                  RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau' q' h c l' n
                      bundle pkg ∧
                    hsame l l' ∧ UnaryHistory realSeal ∧ Cont tau' q' l' ∧
                      Cont l' n realSeal ∧ PkgSig bundle l' pkg ∧
                        PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro packet sameTau sameQ thresholdRoute sealRoute thresholdPkg sealPkg
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, m0Unary, m1Unary, tauUnary,
    qUnary, hUnary, cUnary, _lUnary, nUnary, r0w0Row, r1w1Row, m0m1Row,
    tauqRow, _pkgRow⟩ := packet
  have tauUnary' : UnaryHistory tau' :=
    unary_transport tauUnary sameTau
  have qUnary' : UnaryHistory q' :=
    unary_transport qUnary sameQ
  have lUnary' : UnaryHistory l' :=
    unary_cont_closed tauUnary' qUnary' thresholdRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed lUnary' nUnary sealRoute
  have m0m1Row' : Cont m0 m1 tau' :=
    cont_result_hsame_transport m0m1Row sameTau
  have sameL : hsame l l' :=
    cont_respects_hsame sameTau sameQ tauqRow thresholdRoute
  exact
    ⟨⟨r0Unary, r1Unary, w0Unary, w1Unary, m0Unary, m1Unary, tauUnary',
        qUnary', hUnary, cUnary, lUnary', nUnary, r0w0Row, r1w1Row, m0m1Row',
        thresholdRoute, thresholdPkg⟩,
      sameL, realSealUnary, thresholdRoute, sealRoute, thresholdPkg, sealPkg⟩

end BEDC.Derived.RegularCauchyTailMeetUp
