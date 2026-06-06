import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EquicontinuityFiniteModulusCarrier [AskSetup] [PackageSetup]
    (K F eps rho M G T R P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory eps ∧ UnaryHistory rho ∧
    UnaryHistory M ∧ UnaryHistory G ∧ UnaryHistory T ∧ UnaryHistory R ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont K F eps ∧ Cont eps rho M ∧
        Cont M G R ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem EquicontinuityFiniteModulusCarrier_compactmetric_handoff
    [AskSetup] [PackageSetup]
    {K F eps rho M G T R P N compactRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityFiniteModulusCarrier K F eps rho M G T R P N bundle pkg →
      Cont K F compactRead →
        Cont compactRead rho modulusRead →
          PkgSig bundle modulusRead pkg →
            UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory rho ∧ UnaryHistory M ∧
              UnaryHistory G ∧ UnaryHistory compactRead ∧ UnaryHistory modulusRead ∧
                Cont K F compactRead ∧ Cont compactRead rho modulusRead ∧
                  Cont eps rho M ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle modulusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier compactRoute modulusRoute modulusPkg
  obtain ⟨unaryK, unaryF, _unaryEps, unaryRho, unaryM, unaryG, _unaryT, _unaryR,
    _unaryP, _unaryN, _epsRoute, modulusHandoff, _boundaryRoute, pkgP, _pkgN⟩ :=
    carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed unaryK unaryF compactRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed compactUnary unaryRho modulusRoute
  exact
    ⟨unaryK, unaryF, unaryRho, unaryM, unaryG, compactUnary, modulusUnary,
      compactRoute, modulusRoute, modulusHandoff, pkgP, modulusPkg⟩

end BEDC.Derived.EquicontinuityUp
