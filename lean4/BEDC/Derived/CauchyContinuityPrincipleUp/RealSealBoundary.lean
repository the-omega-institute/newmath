import BEDC.Derived.CauchyContinuityPrincipleUp.TasteGate

namespace BEDC.Derived.CauchyContinuityPrincipleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyContinuityPrincipleCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {source windows tolerance modulus uniformity target sealRow transport replay provenance
      localName windowRead modulusRead uniformityRead targetRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuityPrincipleCarrier source windows tolerance modulus uniformity target sealRow
        transport replay provenance localName bundle pkg ->
      Cont windows tolerance windowRead ->
        Cont windowRead modulus modulusRead ->
          Cont modulusRead uniformity uniformityRead ->
            Cont uniformityRead target targetRead ->
              Cont targetRead sealRow sealRead ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory windows ∧ UnaryHistory tolerance ∧ UnaryHistory modulus ∧
                    UnaryHistory uniformity ∧ UnaryHistory target ∧ UnaryHistory sealRow ∧
                      UnaryHistory windowRead ∧ UnaryHistory modulusRead ∧
                        UnaryHistory uniformityRead ∧ UnaryHistory targetRead ∧
                          UnaryHistory sealRead ∧ Cont windows tolerance windowRead ∧
                            Cont windowRead modulus modulusRead ∧
                              Cont modulusRead uniformity uniformityRead ∧
                                Cont uniformityRead target targetRead ∧
                                  Cont targetRead sealRow sealRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier windowsTolerance windowModulus modulusUniformity uniformityTarget targetSeal
    sealPkg
  obtain ⟨_sourceUnary, windowsUnary, toleranceUnary, modulusUnary, uniformityUnary,
    targetUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
      _localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowsUnary toleranceUnary windowsTolerance
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed windowReadUnary modulusUnary windowModulus
  have uniformityReadUnary : UnaryHistory uniformityRead :=
    unary_cont_closed modulusReadUnary uniformityUnary modulusUniformity
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed uniformityReadUnary targetUnary uniformityTarget
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed targetReadUnary sealRowUnary targetSeal
  exact
    ⟨windowsUnary, toleranceUnary, modulusUnary, uniformityUnary, targetUnary, sealRowUnary,
      windowReadUnary, modulusReadUnary, uniformityReadUnary, targetReadUnary, sealReadUnary,
      windowsTolerance, windowModulus, modulusUniformity, uniformityTarget, targetSeal,
      provenancePkg, sealPkg⟩

end BEDC.Derived.CauchyContinuityPrincipleUp
