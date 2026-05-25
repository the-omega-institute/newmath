import BEDC.Derived.SequentialCompactnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentialCompactnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactnessCarrier_selector_refusal [AskSetup] [PackageSetup]
    {compactSource sequenceWindow selectorWindow readback realSeal transport provenance _localCert
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory compactSource →
      UnaryHistory sequenceWindow →
        UnaryHistory readback →
          UnaryHistory transport →
            Cont compactSource sequenceWindow selectorWindow →
              Cont selectorWindow readback realSeal →
                Cont realSeal transport consumer →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle consumer pkg →
                      UnaryHistory selectorWindow ∧ UnaryHistory realSeal ∧
                        UnaryHistory consumer ∧
                          Cont compactSource sequenceWindow selectorWindow ∧
                            Cont selectorWindow readback realSeal ∧
                              Cont realSeal transport consumer ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro compactUnary sequenceUnary readbackUnary transportUnary selectorCont realSealCont
    consumerCont provenancePkg consumerPkg
  have selectorUnary : UnaryHistory selectorWindow :=
    unary_cont_closed compactUnary sequenceUnary selectorCont
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed selectorUnary readbackUnary realSealCont
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed realSealUnary transportUnary consumerCont
  exact
    ⟨selectorUnary, realSealUnary, consumerUnary, selectorCont, realSealCont, consumerCont,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.SequentialCompactnessUp
