import BEDC.Derived.LocatedOpenUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedOpenUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedOpenCarrier [AskSetup] [PackageSetup]
    (L R S Q W E T H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory Q ∧
    UnaryHistory W ∧ UnaryHistory E ∧ UnaryHistory T ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem LocatedOpenCarrier_window_stability [AskSetup] [PackageSetup]
    {L R S Q W E T H C P N transportedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedOpenCarrier L R S Q W E T H C P N bundle pkg →
      Cont W H transportedWindow →
        UnaryHistory transportedWindow ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig
  intro carrier transport
  obtain ⟨_unaryL, _unaryR, _unaryS, _unaryQ, unaryW, _unaryE, _unaryT,
    unaryH, _unaryC, _unaryP, _unaryN, provenancePkg, namePkg⟩ := carrier
  exact ⟨unary_cont_closed unaryW unaryH transport, provenancePkg, namePkg⟩

end BEDC.Derived.LocatedOpenUp
