import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealBaireCylinderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealBaireCylinderStreamRealHandoff [AskSetup] [PackageSetup]
    {B S Q E H C P N streamRead rationalRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory S ->
        UnaryHistory Q ->
          UnaryHistory E ->
            Cont B S streamRead ->
              Cont streamRead Q rationalRead ->
                Cont rationalRead E sealRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle sealRead pkg ->
                      UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory Q ∧
                        UnaryHistory E ∧ UnaryHistory streamRead ∧
                          UnaryHistory rationalRead ∧ UnaryHistory sealRead ∧
                            Cont B S streamRead ∧ Cont streamRead Q rationalRead ∧
                              Cont rationalRead E sealRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro bUnary sUnary qUnary eUnary streamCont rationalCont sealCont provenancePkg sealPkg
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed bUnary sUnary streamCont
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed streamUnary qUnary rationalCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rationalUnary eUnary sealCont
  exact
    ⟨bUnary, sUnary, qUnary, eUnary, streamUnary, rationalUnary, sealUnary,
      streamCont, rationalCont, sealCont, provenancePkg, sealPkg⟩

end BEDC.Derived.RealBaireCylinderUp
