import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_real_approximation_density_route [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N approximationRoute sealRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont Q W R ->
        Cont R G approximationRoute ->
          Cont approximationRoute E sealRoute ->
            PkgSig bundle sealRoute pkg ->
              UnaryHistory Q ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory G ∧
                UnaryHistory E ∧ UnaryHistory approximationRoute ∧ UnaryHistory sealRoute ∧
                  Cont Q W R ∧ Cont R G approximationRoute ∧
                    Cont approximationRoute E sealRoute ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle sealRoute pkg := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier routeQWR routeRGA routeAES sealPkg
  obtain ⟨_unaryB, _unaryA, _unaryM, _unaryL, _unaryT, _unaryS, _unaryD, unaryQ,
    unaryW, unaryR, unaryG, unaryE, _unaryH, _unaryC, _unaryP, _unaryN, _emptyA,
    _emptyS, _emptyM, _emptyG, _emptyE, carrierPkg⟩ := carrier
  have approximationUnary : UnaryHistory approximationRoute :=
    unary_cont_closed unaryR unaryG routeRGA
  have sealUnary : UnaryHistory sealRoute :=
    unary_cont_closed approximationUnary unaryE routeAES
  exact
    ⟨unaryQ, unaryW, unaryR, unaryG, unaryE, approximationUnary, sealUnary, routeQWR,
      routeRGA, routeAES, carrierPkg, sealPkg⟩

end BEDC.Derived.FareySequenceUp
