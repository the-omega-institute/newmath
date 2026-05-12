import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StationaryRationalCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StationaryRationalCauchyCarrier [AskSetup] [PackageSetup]
    (seed schedule regularMember dyadicLedger realSeal provenance localCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory seed ∧ UnaryHistory schedule ∧ UnaryHistory endpoint ∧
    Cont seed schedule regularMember ∧ Cont regularMember schedule dyadicLedger ∧
      Cont dyadicLedger endpoint realSeal ∧ Cont realSeal localCert provenance ∧
        PkgSig bundle provenance pkg

theorem StationaryRationalCauchyCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {seed schedule regularMember dyadicLedger realSeal provenance localCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalCauchyCarrier seed schedule regularMember dyadicLedger realSeal provenance
        localCert endpoint bundle pkg →
      UnaryHistory seed ∧ UnaryHistory schedule ∧ UnaryHistory regularMember ∧
        UnaryHistory dyadicLedger ∧ UnaryHistory realSeal ∧
          hsame regularMember (append seed schedule) ∧
            hsame dyadicLedger (append regularMember schedule) ∧
              hsame realSeal (append dyadicLedger endpoint) ∧
                PkgSig bundle provenance pkg := by
  intro carrier
  have seedUnary : UnaryHistory seed :=
    carrier.left
  have scheduleUnary : UnaryHistory schedule :=
    carrier.right.left
  have endpointUnary : UnaryHistory endpoint :=
    carrier.right.right.left
  have regularCont : Cont seed schedule regularMember :=
    carrier.right.right.right.left
  have dyadicCont : Cont regularMember schedule dyadicLedger :=
    carrier.right.right.right.right.left
  have realSealCont : Cont dyadicLedger endpoint realSeal :=
    carrier.right.right.right.right.right.left
  have regularUnary : UnaryHistory regularMember :=
    unary_cont_closed seedUnary scheduleUnary regularCont
  have dyadicUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed regularUnary scheduleUnary dyadicCont
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicUnary endpointUnary realSealCont
  have regularSame : hsame regularMember (append seed schedule) :=
    regularCont
  have dyadicSame : hsame dyadicLedger (append regularMember schedule) :=
    dyadicCont
  have realSealSame : hsame realSeal (append dyadicLedger endpoint) :=
    realSealCont
  exact
    And.intro seedUnary
      (And.intro scheduleUnary
        (And.intro regularUnary
          (And.intro dyadicUnary
            (And.intro realSealUnary
              (And.intro regularSame
                (And.intro dyadicSame
                  (And.intro realSealSame
                    carrier.right.right.right.right.right.right.right)))))))

end BEDC.Derived.StationaryRationalCauchyUp
