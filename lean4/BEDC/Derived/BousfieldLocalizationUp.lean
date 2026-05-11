import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BousfieldLocalizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BousfieldLocalizationEmptySelectedMap_boundary [AskSetup] [PackageSetup]
    {model selected localRow transport provenance certRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory model -> UnaryHistory localRow -> UnaryHistory provenance ->
      hsame selected BHist.Empty -> Cont model selected transport ->
        Cont transport localRow certRow -> PkgSig bundle certRow pkg ->
          hsame transport model ∧ UnaryHistory certRow ∧
            Cont transport localRow certRow ∧ PkgSig bundle certRow pkg := by
  intro modelUnary localUnary _provenanceUnary selectedEmpty transportRow certRowCont pkgSig
  cases selectedEmpty
  have transportSame : hsame transport model :=
    cont_deterministic transportRow (cont_right_unit model)
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed modelUnary unary_empty transportRow
  have certRowUnary : UnaryHistory certRow :=
    unary_cont_closed transportUnary localUnary certRowCont
  exact And.intro transportSame
    (And.intro certRowUnary (And.intro certRowCont pkgSig))

end BEDC.Derived.BousfieldLocalizationUp
