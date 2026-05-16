import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_regseqrat_uniform_consumer_exhaustion
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name consumerRead
      sealRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail consumerRead →
        Cont tail sealRow sealRead →
          Cont consumerRead sealRead finalRead →
            PkgSig bundle consumerRead pkg →
              PkgSig bundle sealRead pkg →
                PkgSig bundle finalRead pkg →
                  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory consumerRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory finalRead ∧
                        Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                          Cont index tail consumerRead ∧ Cont tail sealRow sealRead ∧
                            Cont consumerRead sealRead finalRead ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailConsumer tailSealRead consumerSealFinal _consumerPkg _sealPkg finalPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed indexUnary tailUnary indexTailConsumer
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed consumerUnary sealUnary consumerSealFinal
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, consumerUnary,
      sealUnary, finalUnary, indexWindowsModulus, modulusToleranceTail, indexTailConsumer,
      tailSealRead, consumerSealFinal, namePkg, finalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
