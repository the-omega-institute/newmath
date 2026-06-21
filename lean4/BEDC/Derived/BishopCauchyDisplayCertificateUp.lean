import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopCauchyDisplayCertificateUp [AskSetup] [PackageSetup]
    (criterion modulus windows tail readback dyadic realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory criterion /\
    UnaryHistory modulus /\
      UnaryHistory windows /\
        UnaryHistory tail /\
          UnaryHistory readback /\
            UnaryHistory dyadic /\
              UnaryHistory realSeal /\
                UnaryHistory transport /\
                  UnaryHistory replay /\
                    UnaryHistory provenance /\
                      UnaryHistory localName /\
                        Cont criterion modulus windows /\
                          Cont windows tail readback /\
                            Cont readback dyadic realSeal /\
                              PkgSig bundle provenance pkg /\
                                PkgSig bundle localName pkg

namespace BishopCauchyDisplayCertificateUp

theorem BishopCauchyDisplayCertificateCarrier_tail_handoff [AskSetup] [PackageSetup]
    {criterion modulus windows tail readback dyadic realSeal transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.BishopCauchyDisplayCertificateUp criterion modulus windows tail readback
        dyadic realSeal transport replay provenance localName bundle pkg ->
      UnaryHistory criterion /\
        UnaryHistory modulus /\
          UnaryHistory windows /\
            UnaryHistory tail /\
              UnaryHistory readback /\
                UnaryHistory dyadic /\
                  UnaryHistory realSeal /\
                    Cont criterion modulus windows /\
                      Cont windows tail readback /\
                        Cont readback dyadic realSeal /\
                          PkgSig bundle provenance pkg /\
                            PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier
  obtain ⟨criterionUnary, modulusUnary, windowsUnary, tailUnary, readbackUnary,
    dyadicUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, criterionModulusWindows, windowsTailReadback,
    readbackDyadicRealSeal, provenancePkg, localNamePkg⟩ := carrier
  exact
    ⟨criterionUnary, modulusUnary, windowsUnary, tailUnary, readbackUnary,
      dyadicUnary, realSealUnary, criterionModulusWindows, windowsTailReadback,
      readbackDyadicRealSeal, provenancePkg, localNamePkg⟩

end BishopCauchyDisplayCertificateUp
end BEDC.Derived
