import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_shared_schedule_real_seal_inheritance
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name singletonTail
      pairTail singletonSeal pairSeal singletonRead pairRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail singletonTail ->
        Cont index tail pairTail ->
          Cont tail sealRow singletonSeal ->
            Cont tail sealRow pairSeal ->
              Cont singletonTail singletonSeal singletonRead ->
                Cont pairTail pairSeal pairRead ->
                  PkgSig bundle singletonRead pkg ->
                    PkgSig bundle pairRead pkg ->
                      UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                        UnaryHistory tail ∧ UnaryHistory singletonTail ∧
                          UnaryHistory pairTail ∧ UnaryHistory singletonSeal ∧
                            UnaryHistory pairSeal ∧ UnaryHistory singletonRead ∧
                              UnaryHistory pairRead ∧ Cont index windows modulus ∧
                                Cont modulus tolerance tail ∧ Cont index tail singletonTail ∧
                                  Cont index tail pairTail ∧ Cont tail sealRow singletonSeal ∧
                                    Cont tail sealRow pairSeal ∧
                                      Cont singletonTail singletonSeal singletonRead ∧
                                        Cont pairTail pairSeal pairRead ∧
                                          hsame singletonTail pairTail ∧
                                            hsame singletonSeal pairSeal ∧
                                              PkgSig bundle name pkg ∧
                                                PkgSig bundle singletonRead pkg ∧
                                                  PkgSig bundle pairRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet singletonTailRoute pairTailRoute singletonSealRoute pairSealRoute
    singletonReadRoute pairReadRoute singletonReadPkg pairReadPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have singletonTailUnary : UnaryHistory singletonTail :=
    unary_cont_closed indexUnary tailUnary singletonTailRoute
  have pairTailUnary : UnaryHistory pairTail :=
    unary_cont_closed indexUnary tailUnary pairTailRoute
  have singletonSealUnary : UnaryHistory singletonSeal :=
    unary_cont_closed tailUnary sealRowUnary singletonSealRoute
  have pairSealUnary : UnaryHistory pairSeal :=
    unary_cont_closed tailUnary sealRowUnary pairSealRoute
  have singletonReadUnary : UnaryHistory singletonRead :=
    unary_cont_closed singletonTailUnary singletonSealUnary singletonReadRoute
  have pairReadUnary : UnaryHistory pairRead :=
    unary_cont_closed pairTailUnary pairSealUnary pairReadRoute
  have sameTail : hsame singletonTail pairTail :=
    cont_respects_hsame (hsame_refl index) (hsame_refl tail) singletonTailRoute
      pairTailRoute
  have sameSeal : hsame singletonSeal pairSeal :=
    cont_respects_hsame (hsame_refl tail) (hsame_refl sealRow) singletonSealRoute
      pairSealRoute
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, tailUnary, singletonTailUnary, pairTailUnary,
      singletonSealUnary, pairSealUnary, singletonReadUnary, pairReadUnary,
      indexWindowsModulus, modulusToleranceTail, singletonTailRoute, pairTailRoute,
      singletonSealRoute, pairSealRoute, singletonReadRoute, pairReadRoute, sameTail,
      sameSeal, namePkg, singletonReadPkg, pairReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
