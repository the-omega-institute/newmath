import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.MooreSmithConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MooreSmithConvergencePacket [AskSetup] [PackageSetup]
    (D V U C B R L H K P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory D ∧ UnaryHistory V ∧ UnaryHistory U ∧ UnaryHistory C ∧
    UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory L ∧ UnaryHistory H ∧
      UnaryHistory K ∧ UnaryHistory N ∧ Cont D V U ∧ Cont U C B ∧
        Cont B R L ∧ PkgSig bundle P pkg

theorem MooreSmithConvergencePacket_namecert_obligations [AskSetup] [PackageSetup]
    {D V U C B R L H K P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreSmithConvergencePacket D V U C B R L H K P N bundle pkg ->
      UnaryHistory D ∧ UnaryHistory V ∧ UnaryHistory U ∧ UnaryHistory C ∧
        UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory L ∧ Cont D V U ∧
          Cont U C B ∧ Cont B R L ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet
  obtain ⟨dUnary, vUnary, uUnary, cUnary, bUnary, rUnary, lUnary, _hUnary,
    _kUnary, _nUnary, dvu, ucb, brl, pPkg⟩ := packet
  exact
    ⟨dUnary, vUnary, uUnary, cUnary, bUnary, rUnary, lUnary, dvu, ucb, brl,
      pPkg⟩

end BEDC.Derived.MooreSmithConvergenceUp
