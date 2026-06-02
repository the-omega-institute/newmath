import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevFiniteWindowCarrier_field_faithful [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient trace transports provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevFiniteWindowCarrier domain base codomain magnitude gradient trace transports
        provenance localCert bundle pkg ->
      UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
        UnaryHistory magnitude ∧ UnaryHistory gradient ∧ UnaryHistory trace ∧
          UnaryHistory transports ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
            Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
              Cont gradient trace transports ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: SobolevFiniteWindowCarrier BHist Cont ProbeBundle PkgSig
  intro carrier
  exact carrier

end BEDC.Derived.SobolevUp
