import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailBoundUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyTailBoundCarrier [AskSetup] [PackageSetup]
    (threshold stream dyadic readback realSeal tailBound transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory threshold ∧
    UnaryHistory stream ∧
      UnaryHistory dyadic ∧
        UnaryHistory tailBound ∧
          UnaryHistory transport ∧
            UnaryHistory replay ∧
              Cont threshold stream dyadic ∧
                Cont stream dyadic readback ∧
                  Cont readback tailBound realSeal ∧
                    Cont transport replay provenance ∧
                      PkgSig bundle provenance pkg ∧
                        PkgSig bundle localName pkg

theorem CauchyTailBoundCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {threshold stream dyadic readback realSeal tailBound transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailBoundCarrier threshold stream dyadic readback realSeal tailBound transport
        replay provenance localName bundle pkg →
      UnaryHistory threshold ∧
        UnaryHistory stream ∧
          UnaryHistory dyadic ∧
            UnaryHistory readback ∧
              UnaryHistory realSeal ∧
                UnaryHistory tailBound ∧
                  Cont threshold stream dyadic ∧
                    Cont stream dyadic readback ∧
                      Cont readback tailBound realSeal ∧
                        Cont transport replay provenance ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier
  obtain ⟨thresholdUnary, streamUnary, dyadicUnary, tailBoundUnary, transportUnary,
    replayUnary, thresholdStreamDyadic, streamDyadicReadback, readbackTailRealSeal,
    transportReplayProvenance, provenancePkg, localNamePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary tailBoundUnary readbackTailRealSeal
  exact
    ⟨thresholdUnary, streamUnary, dyadicUnary, readbackUnary, realSealUnary,
      tailBoundUnary, thresholdStreamDyadic, streamDyadicReadback, readbackTailRealSeal,
      transportReplayProvenance, provenancePkg, localNamePkg⟩

end BEDC.Derived.CauchyTailBoundUp
