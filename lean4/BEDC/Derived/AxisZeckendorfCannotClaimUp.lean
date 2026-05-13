import BEDC.Derived.AxisZeckendorf
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxisZeckendorfCannotClaimRegistryPacket [AskSetup] [PackageSetup]
    (a b c d e f g h p n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory a ∧
    UnaryHistory b ∧
      UnaryHistory c ∧
        UnaryHistory d ∧
          UnaryHistory e ∧
            UnaryHistory f ∧
              UnaryHistory g ∧
                Cont a b h ∧
                  Cont c d h ∧ Cont e f h ∧ hsame p n ∧ PkgSig bundle p pkg

theorem AxisZeckendorfCannotClaimRegistryPacket_source_row_coverage [AskSetup] [PackageSetup]
    {a b c d e f g h p n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory c ∧ UnaryHistory d ∧
        UnaryHistory e ∧ UnaryHistory f ∧ UnaryHistory g ∧ Cont a b h ∧ Cont c d h ∧
          Cont e f h ∧ hsame p n ∧ PkgSig bundle p pkg := by
  intro packet
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD, routeEF,
      sameProvenanceName, pkgSig⟩ := packet
  exact
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD, routeEF,
      sameProvenanceName, pkgSig⟩

theorem AxisZeckendorfCannotClaimRegistryPacket_transport_nonpromotion [AskSetup] [PackageSetup]
    {a b c d e f g h p n a' b' c' d' e' f' g' h' p' n' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      hsame a a' ->
        hsame b b' ->
          hsame c c' ->
            hsame d d' ->
              hsame e e' ->
                hsame f f' ->
                  hsame g g' ->
                    hsame p p' ->
                      hsame n n' ->
                        Cont a' b' h' ->
                          Cont c' d' h' ->
                            Cont e' f' h' ->
                              PkgSig bundle p' pkg ->
                                AxisZeckendorfCannotClaimRegistryPacket a' b' c' d' e' f'
                                    g' h' p' n' bundle pkg ∧
                                  hsame h h' ∧ hsame p' n' := by
  intro packet sameA sameB sameC sameD sameE sameF sameG sameP sameN routeAB' routeCD'
    routeEF' pkgSig'
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, _routeCD, _routeEF,
      sameProvenanceName, _pkgSig⟩ := packet
  have routeSame : hsame h h' := cont_respects_hsame sameA sameB routeAB routeAB'
  have transportedProvenanceName : hsame p' n' :=
    hsame_trans (hsame_symm sameP) (hsame_trans sameProvenanceName sameN)
  constructor
  · exact
      ⟨unary_transport aUnary sameA, unary_transport bUnary sameB,
        unary_transport cUnary sameC, unary_transport dUnary sameD,
        unary_transport eUnary sameE, unary_transport fUnary sameF,
        unary_transport gUnary sameG, routeAB', routeCD', routeEF', transportedProvenanceName,
        pkgSig'⟩
  · exact ⟨routeSame, transportedProvenanceName⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
