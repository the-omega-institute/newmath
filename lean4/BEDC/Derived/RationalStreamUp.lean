import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalStreamPacket [AskSetup] [PackageSetup]
    (index schedule rationalRows classifierRows transportWindow consumerRoute certRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory index ∧ UnaryHistory schedule ∧ UnaryHistory rationalRows ∧
    UnaryHistory classifierRows ∧ UnaryHistory transportWindow ∧
      UnaryHistory consumerRoute ∧ UnaryHistory certRow ∧
        Cont index schedule transportWindow ∧
          Cont rationalRows classifierRows consumerRoute ∧
            Cont transportWindow consumerRoute certRow ∧ PkgSig bundle certRow pkg

theorem RationalStreamPacket_pointwise_rat_obligations [AskSetup] [PackageSetup]
    {index schedule rationalRows classifierRows transportWindow consumerRoute certRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalStreamPacket index schedule rationalRows classifierRows transportWindow consumerRoute
        certRow bundle pkg ->
      UnaryHistory index ∧ UnaryHistory rationalRows ∧ UnaryHistory classifierRows ∧
        Cont rationalRows classifierRows consumerRoute ∧
          Cont transportWindow consumerRoute certRow ∧ PkgSig bundle certRow pkg := by
  intro packet
  cases packet with
  | intro indexUnary rest =>
      cases rest with
      | intro _scheduleUnary rest =>
          cases rest with
          | intro rationalUnary rest =>
              cases rest with
              | intro classifierUnary rest =>
                  cases rest with
                  | intro _transportUnary rest =>
                      cases rest with
                      | intro _consumerUnary rest =>
                          cases rest with
                          | intro _certUnary rest =>
                              cases rest with
                              | intro _transportWindowRow rest =>
                                  cases rest with
                                  | intro consumerRouteRow rest =>
                                      cases rest with
                                      | intro certRowRow pkgSig =>
                                          exact
                                            ⟨indexUnary, rationalUnary, classifierUnary,
                                              consumerRouteRow, certRowRow, pkgSig⟩

end BEDC.Derived.RationalStreamUp
