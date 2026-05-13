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

end BEDC.Derived.AxisZeckendorfCannotClaimUp
