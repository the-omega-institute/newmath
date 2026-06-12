import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalIntervalRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem RationalIntervalRefinementLedgerExhaustion [AskSetup] [PackageSetup]
    {I J E W K H C P N finalRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalRefinementCarrier I J E W K H C P N bundle pkg ->
      Cont E W finalRead -> Cont finalRead K publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row I ∨ hsame row J ∨ hsame row E ∨ hsame row W ∨
                  hsame row K ∨ hsame row finalRead ∨ hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont I J E ∧ Cont E W finalRead ∧
                  Cont finalRead K publicRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg ∧ PkgSig bundle publicRead pkg)
              hsame ∧ UnaryHistory finalRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier finalRoute publicRoute publicPkg
  cases carrier with
  | intro _unaryI rest =>
      cases rest with
      | intro _unaryJ rest =>
          cases rest with
          | intro unaryE rest =>
              cases rest with
              | intro unaryW rest =>
                  cases rest with
                  | intro unaryK rest =>
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
                                          | intro _contEWK rest =>
                                              cases rest with
                                              | intro _contKHC rest =>
                                                  cases rest with
                                                  | intro pkgP pkgN =>
                                                      have finalUnary :
                                                          UnaryHistory finalRead :=
                                                        unary_cont_closed unaryE unaryW
                                                          finalRoute
                                                      have publicUnary :
                                                          UnaryHistory publicRead :=
                                                        unary_cont_closed finalUnary unaryK
                                                          publicRoute
                                                      have sourcePublic :
                                                          (fun row : BHist =>
                                                            hsame row publicRead ∧
                                                              UnaryHistory row)
                                                              publicRead :=
                                                        ⟨hsame_refl publicRead,
                                                          publicUnary⟩
                                                      have cert :
                                                          SemanticNameCert
                                                              (fun row : BHist =>
                                                                hsame row publicRead ∧
                                                                  UnaryHistory row)
                                                              (fun row : BHist =>
                                                                hsame row I ∨
                                                                  hsame row J ∨
                                                                    hsame row E ∨
                                                                      hsame row W ∨
                                                                        hsame row K ∨
                                                                          hsame row
                                                                            finalRead ∨
                                                                            hsame row
                                                                              publicRead)
                                                              (fun row : BHist =>
                                                                UnaryHistory row ∧
                                                                  Cont I J E ∧
                                                                    Cont E W finalRead ∧
                                                                      Cont finalRead K
                                                                        publicRead ∧
                                                                        PkgSig bundle P
                                                                          pkg ∧
                                                                          PkgSig bundle N
                                                                            pkg ∧
                                                                            PkgSig bundle
                                                                              publicRead
                                                                              pkg)
                                                              hsame := {
                                                        core := {
                                                          carrier_inhabited :=
                                                            Exists.intro publicRead
                                                              sourcePublic
                                                          equiv_refl := by
                                                            intro row _source
                                                            exact hsame_refl row
                                                          equiv_symm := by
                                                            intro _row _other sameRows
                                                            exact hsame_symm sameRows
                                                          equiv_trans := by
                                                            intro _row _middle _other
                                                              sameLeft sameRight
                                                            exact
                                                              hsame_trans sameLeft
                                                                sameRight
                                                          carrier_respects_equiv := by
                                                            intro _row other sameRows
                                                              source
                                                            exact
                                                              ⟨hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  source.left,
                                                                unary_transport
                                                                  source.right
                                                                  sameRows⟩
                                                        }
                                                        pattern_sound := by
                                                          intro _row source
                                                          exact
                                                            Or.inr
                                                              (Or.inr
                                                                (Or.inr
                                                                  (Or.inr
                                                                    (Or.inr
                                                                      (Or.inr
                                                                        source.left)))))
                                                        ledger_sound := by
                                                          intro _row source
                                                          exact
                                                            ⟨source.right, contIJE,
                                                              finalRoute, publicRoute,
                                                              pkgP, pkgN, publicPkg⟩
                                                      }
                                                      exact ⟨cert, finalUnary, publicUnary⟩

theorem RationalIntervalRefinementNameCertObligations [AskSetup] [PackageSetup]
    {I J E W K H C P N publicRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalRefinementCarrier I J E W K H C P N bundle pkg →
      Cont E W publicRead → PkgSig bundle publicRead pkg →
        SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row I ∨ hsame row J ∨ hsame row E ∨ hsame row W ∨
                hsame row K ∨ hsame row publicRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont I J E ∧ Cont E W publicRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle publicRead pkg)
            hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier publicRoute publicPkg
  cases carrier with
  | intro _unaryI rest =>
      cases rest with
      | intro _unaryJ rest =>
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
                                          | intro _contEWK rest =>
                                              cases rest with
                                              | intro _contKHC rest =>
                                                  cases rest with
                                                  | intro pkgP pkgN =>
                                                      have publicUnary :
                                                          UnaryHistory publicRead :=
                                                        unary_cont_closed unaryE unaryW
                                                          publicRoute
                                                      have sourcePublic :
                                                          (fun row : BHist =>
                                                            hsame row publicRead ∧
                                                              UnaryHistory row)
                                                              publicRead :=
                                                        ⟨hsame_refl publicRead,
                                                          publicUnary⟩
                                                      have cert :
                                                          SemanticNameCert
                                                              (fun row : BHist =>
                                                                hsame row publicRead ∧
                                                                  UnaryHistory row)
                                                              (fun row : BHist =>
                                                                hsame row I ∨
                                                                  hsame row J ∨
                                                                    hsame row E ∨
                                                                      hsame row W ∨
                                                                        hsame row K ∨
                                                                          hsame row
                                                                            publicRead)
                                                              (fun row : BHist =>
                                                                UnaryHistory row ∧
                                                                  Cont I J E ∧
                                                                    Cont E W publicRead ∧
                                                                      PkgSig bundle P
                                                                        pkg ∧
                                                                        PkgSig bundle N
                                                                          pkg ∧
                                                                          PkgSig bundle
                                                                            publicRead
                                                                            pkg)
                                                              hsame := {
                                                        core := {
                                                          carrier_inhabited :=
                                                            Exists.intro publicRead
                                                              sourcePublic
                                                          equiv_refl := by
                                                            intro row _source
                                                            exact hsame_refl row
                                                          equiv_symm := by
                                                            intro _row _other sameRows
                                                            exact hsame_symm sameRows
                                                          equiv_trans := by
                                                            intro _row _middle _other
                                                              sameLeft sameRight
                                                            exact
                                                              hsame_trans sameLeft
                                                                sameRight
                                                          carrier_respects_equiv := by
                                                            intro _row other sameRows
                                                              source
                                                            exact
                                                              ⟨hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  source.left,
                                                                unary_transport
                                                                  source.right
                                                                  sameRows⟩
                                                        }
                                                        pattern_sound := by
                                                          intro _row source
                                                          exact
                                                            Or.inr
                                                              (Or.inr
                                                                (Or.inr
                                                                  (Or.inr
                                                                    (Or.inr source.left))))
                                                        ledger_sound := by
                                                          intro _row source
                                                          exact
                                                            ⟨source.right, contIJE,
                                                              publicRoute, pkgP, pkgN,
                                                              publicPkg⟩
                                                      }
                                                      exact ⟨cert, publicUnary⟩

theorem RationalIntervalRefinementWindowBranchExhaustion [AskSetup] [PackageSetup]
    {I0 J0 E0 W0 K0 H0 C0 P0 N0 I1 J1 E1 W1 K1 H1 C1 P1 N1 retained
      branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalRefinementCarrier I0 J0 E0 W0 K0 H0 C0 P0 N0 bundle pkg →
      RationalIntervalRefinementCarrier I1 J1 E1 W1 K1 H1 C1 P1 N1 bundle pkg →
        hsame J0 I1 → Cont W0 W1 retained → Cont retained K1 branchRead →
          PkgSig bundle branchRead pkg →
            UnaryHistory retained ∧ UnaryHistory branchRead ∧ Cont W0 W1 retained ∧
              Cont retained K1 branchRead ∧ hsame J0 I1 ∧ PkgSig bundle P0 pkg ∧
                PkgSig bundle N1 pkg ∧ PkgSig bundle branchRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory PkgSig
  intro carrier0 carrier1 sameLink retainedRoute branchRoute branchPkg
  cases carrier0 with
  | intro _unaryI0 rest0 =>
      cases rest0 with
      | intro _unaryJ0 rest0 =>
          cases rest0 with
          | intro _unaryE0 rest0 =>
              cases rest0 with
              | intro unaryW0 rest0 =>
                  cases rest0 with
                  | intro _unaryK0 rest0 =>
                      cases rest0 with
                      | intro _unaryH0 rest0 =>
                          cases rest0 with
                          | intro _unaryC0 rest0 =>
                              cases rest0 with
                              | intro _unaryP0 rest0 =>
                                  cases rest0 with
                                  | intro _unaryN0 rest0 =>
                                      cases rest0 with
                                      | intro _contIJE0 rest0 =>
                                          cases rest0 with
                                          | intro _contEWK0 rest0 =>
                                              cases rest0 with
                                              | intro _contKHC0 rest0 =>
                                                  cases rest0 with
                                                  | intro pkgP0 _pkgN0 =>
                                                      cases carrier1 with
                                                      | intro _unaryI1 rest1 =>
                                                          cases rest1 with
                                                          | intro _unaryJ1 rest1 =>
                                                              cases rest1 with
                                                              | intro _unaryE1 rest1 =>
                                                                  cases rest1 with
                                                                  | intro unaryW1 rest1 =>
                                                                      cases rest1 with
                                                                      | intro unaryK1 rest1 =>
                                                                          cases rest1 with
                                                                          | intro _unaryH1 rest1 =>
                                                                              cases rest1 with
                                                                              | intro _unaryC1 rest1 =>
                                                                                  cases rest1 with
                                                                                  | intro _unaryP1 rest1 =>
                                                                                      cases rest1 with
                                                                                      | intro _unaryN1 rest1 =>
                                                                                          cases rest1 with
                                                                                          | intro _contIJE1 rest1 =>
                                                                                              cases rest1 with
                                                                                              | intro _contEWK1 rest1 =>
                                                                                                  cases rest1 with
                                                                                                  | intro _contKHC1 rest1 =>
                                                                                                      cases rest1 with
                                                                                                      | intro _pkgP1 pkgN1 =>
                                                                                                          have unaryRetained :
                                                                                                              UnaryHistory retained :=
                                                                                                            unary_cont_closed
                                                                                                              unaryW0
                                                                                                              unaryW1
                                                                                                              retainedRoute
                                                                                                          have unaryBranch :
                                                                                                              UnaryHistory branchRead :=
                                                                                                            unary_cont_closed
                                                                                                              unaryRetained
                                                                                                              unaryK1
                                                                                                              branchRoute
                                                                                                          exact
                                                                                                            ⟨unaryRetained,
                                                                                                              unaryBranch,
                                                                                                              retainedRoute,
                                                                                                              branchRoute,
                                                                                                              sameLink,
                                                                                                              pkgP0,
                                                                                                              pkgN1,
                                                                                                              branchPkg⟩

end BEDC.Derived.RationalIntervalRefinementUp
