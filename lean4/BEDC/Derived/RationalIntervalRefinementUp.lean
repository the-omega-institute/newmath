import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalIntervalRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalIntervalRefinementCarrier [AskSetup] [PackageSetup]
    (I J E W K H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory I ∧ UnaryHistory J ∧ UnaryHistory E ∧ UnaryHistory W ∧
    UnaryHistory K ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont I J E ∧ Cont E W K ∧ Cont K H C ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RationalIntervalRefinementCarrier_nested_window [AskSetup] [PackageSetup]
    {I J E W K H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalRefinementCarrier I J E W K H C P N bundle pkg →
      UnaryHistory E ∧ UnaryHistory K ∧ UnaryHistory C ∧ Cont I J E ∧
        Cont E W K ∧ Cont K H C ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier
  cases carrier with
  | intro _IUnary rest =>
      cases rest with
      | intro _JUnary rest =>
          cases rest with
          | intro EUnary rest =>
              cases rest with
              | intro _WUnary rest =>
                  cases rest with
                  | intro KUnary rest =>
                      cases rest with
                      | intro _HUnary rest =>
                          cases rest with
                          | intro CUnary rest =>
                              cases rest with
                              | intro _PUnary rest =>
                                  cases rest with
                                  | intro _NUnary rest =>
                                      cases rest with
                                      | intro IJE rest =>
                                          cases rest with
                                          | intro EWK rest =>
                                              cases rest with
                                              | intro KHC rest =>
                                                  cases rest with
                                                  | intro pkgP pkgN =>
                                                      exact
                                                        ⟨EUnary, KUnary, CUnary, IJE, EWK,
                                                          KHC, pkgP, pkgN⟩

end BEDC.Derived.RationalIntervalRefinementUp
