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

theorem RationalIntervalRefinementCarrier_classifier_stability [AskSetup] [PackageSetup]
    {I J E W K H C P N I' J' E' W' K' H' C' P' N' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalRefinementCarrier I J E W K H C P N bundle pkg ->
      hsame I I' -> hsame J J' -> hsame E E' -> hsame W W' -> hsame K K' ->
        hsame H H' -> hsame C C' -> hsame P P' -> hsame N N' -> Cont I' J' E' ->
          Cont E' W' K' -> Cont K' H' C' -> PkgSig bundle P' pkg ->
            PkgSig bundle N' pkg ->
              RationalIntervalRefinementCarrier I' J' E' W' K' H' C' P' N' bundle pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory PkgSig
  intro carrier sameI sameJ sameE sameW sameK sameH sameC sameP sameN contIJE contEWK
    contKHC pkgP pkgN
  cases carrier with
  | intro unaryI rest =>
      cases rest with
      | intro unaryJ rest =>
          cases rest with
          | intro unaryE rest =>
              cases rest with
              | intro unaryW rest =>
                  cases rest with
                  | intro unaryK rest =>
                      cases rest with
                      | intro unaryH rest =>
                          cases rest with
                          | intro unaryC rest =>
                              cases rest with
                              | intro unaryP rest =>
                                  cases rest with
                                  | intro unaryN _rows =>
                                      exact
                                        ⟨unary_transport unaryI sameI,
                                          unary_transport unaryJ sameJ,
                                          unary_transport unaryE sameE,
                                          unary_transport unaryW sameW,
                                          unary_transport unaryK sameK,
                                          unary_transport unaryH sameH,
                                          unary_transport unaryC sameC,
                                          unary_transport unaryP sameP,
                                          unary_transport unaryN sameN, contIJE, contEWK,
                                          contKHC, pkgP, pkgN⟩

theorem RationalIntervalRefinementCarrier_endpoint_exactness [AskSetup] [PackageSetup]
    {I J E W K H C P N publicRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalRefinementCarrier I J E W K H C P N bundle pkg ->
      Cont E W publicRead -> PkgSig bundle publicRead pkg ->
        UnaryHistory I ∧ UnaryHistory J ∧ UnaryHistory E ∧ UnaryHistory W ∧
          UnaryHistory publicRead ∧ Cont I J E ∧ Cont E W K ∧ Cont E W publicRead ∧
            PkgSig bundle N pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier publicRow publicPkg
  cases carrier with
  | intro unaryI rest =>
      cases rest with
      | intro unaryJ rest =>
          cases rest with
          | intro unaryE rest =>
              cases rest with
              | intro unaryW rest =>
                  cases rest with
                  | intro _unaryK rest =>
                      cases rest with
                      | intro _unaryH rest =>
                          cases rest with
                          | intro _unaryC rest =>
                              cases rest with
                              | intro _unaryP rest =>
                                  cases rest with
                                  | intro _unaryN rest =>
                                      cases rest with
                                      | intro contIJE rest =>
                                          cases rest with
                                          | intro contEWK rest =>
                                              cases rest with
                                              | intro _contKHC rest =>
                                                  cases rest with
                                                  | intro _pkgP pkgN =>
                                                      have unaryPublic :
                                                          UnaryHistory publicRead :=
                                                        unary_cont_closed unaryE unaryW
                                                          publicRow
                                                      exact
                                                        ⟨unaryI, unaryJ, unaryE, unaryW,
                                                          unaryPublic, contIJE, contEWK,
                                                          publicRow, pkgN, publicPkg⟩

end BEDC.Derived.RationalIntervalRefinementUp
