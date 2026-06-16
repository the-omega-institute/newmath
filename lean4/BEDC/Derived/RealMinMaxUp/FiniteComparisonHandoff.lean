import BEDC.Derived.RealMinMaxUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealMinMaxUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealMinMaxCarrier [AskSetup] [PackageSetup]
    (left right minRow maxRow : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: RealMinMaxUp BHist ProbeBundle Pkg UnaryHistory PkgSig
  ∃ RX RY SX SY D E C O H T provenance localName : BHist,
    realMinMaxFields
        (RealMinMaxUp.mk left right RX RY SX SY D E C O minRow maxRow H T provenance
          localName) =
      [left, right, RX, RY, SX, SY, D, E, C, O, minRow, maxRow, H, T, provenance,
        localName] ∧
      UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory minRow ∧
        UnaryHistory maxRow ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem RealMinMaxCarrier_finite_comparison_handoff [AskSetup] [PackageSetup]
    {left right minRow maxRow comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealMinMaxCarrier left right minRow maxRow bundle pkg →
      Cont left right comparisonRead →
        PkgSig bundle comparisonRead pkg →
          UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory comparisonRead ∧
            Cont left right comparisonRead ∧ PkgSig bundle comparisonRead pkg := by
  -- BEDC touchpoint anchor: RealMinMaxCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier comparisonRoute comparisonPkg
  obtain ⟨RX, RY, SX, SY, D, E, C, O, H, T, provenance, localName, _fields,
    leftUnary, rightUnary, _minUnary, _maxUnary, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed leftUnary rightUnary comparisonRoute
  exact ⟨leftUnary, rightUnary, comparisonUnary, comparisonRoute, comparisonPkg⟩

end BEDC.Derived.RealMinMaxUp
