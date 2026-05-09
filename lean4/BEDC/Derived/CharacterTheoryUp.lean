import BEDC.Derived.GroupUp
import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CharacterTheoryUp

open BEDC.Derived.GroupUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CharacterTheoryRootCarrier_obligation [AskSetup] [PackageSetup]
    {group vector action trace ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GroupSingletonCarrier group ->
      VecSpaceSingletonCarrier vector ->
        Cont group vector action ->
          Cont action BHist.Empty trace ->
            PkgSig bundle ledger pkg ->
              GroupSingletonCarrier group ∧ VecSpaceSingletonCarrier vector ∧
                hsame action BHist.Empty ∧ hsame trace BHist.Empty ∧
                  PkgSig bundle ledger pkg := by
  intro groupCarrier vectorCarrier actionCont traceCont pkgSig
  have actionEmpty : hsame action BHist.Empty := by
    exact actionCont.trans (append_eq_empty_iff.mpr (And.intro groupCarrier vectorCarrier))
  have traceAction : hsame trace action :=
    cont_right_unit_result traceCont
  have traceEmpty : hsame trace BHist.Empty :=
    hsame_trans traceAction actionEmpty
  exact And.intro groupCarrier
    (And.intro vectorCarrier
      (And.intro actionEmpty
        (And.intro traceEmpty pkgSig)))

end BEDC.Derived.CharacterTheoryUp
