import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_tail_fiber_seal_compatibility [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailFiber
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont modulus tolerance tailFiber ->
        Cont tailFiber sealRow sealRead ->
          PkgSig bundle sealRead pkg ->
            UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
              UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory tailFiber ∧
                UnaryHistory sealRead ∧ Cont index windows modulus ∧
                  Cont modulus tolerance tail ∧ Cont modulus tolerance tailFiber ∧
                    Cont tailFiber sealRow sealRead ∧ hsame tail tailFiber ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet modulusToleranceTailFiber tailFiberSealRead sealReadPkg
  rcases packet with
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
      modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩
  have tailFiberUnary : UnaryHistory tailFiber :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceTailFiber
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailFiberUnary sealRowUnary tailFiberSealRead
  have tailSame : hsame tail tailFiber :=
    cont_respects_hsame (hsame_refl modulus) (hsame_refl tolerance) modulusToleranceTail
      modulusToleranceTailFiber
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, tailFiberUnary,
      sealReadUnary, indexWindowsModulus, modulusToleranceTail, modulusToleranceTailFiber,
      tailFiberSealRead, tailSame, namePkg, sealReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
