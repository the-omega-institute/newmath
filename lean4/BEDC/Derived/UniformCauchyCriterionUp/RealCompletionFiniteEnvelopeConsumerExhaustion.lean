import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_completion_finite_envelope_consumer_exhaustion
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      sourceRead toleranceRead meetRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows windowRead ->
        Cont windowRead tail sourceRead ->
          Cont modulus tolerance toleranceRead ->
            Cont toleranceRead tail meetRead ->
              Cont meetRead sealRow completionRead ->
                PkgSig bundle sourceRead pkg ->
                  PkgSig bundle toleranceRead pkg ->
                    PkgSig bundle meetRead pkg ->
                      PkgSig bundle completionRead pkg ->
                        UnaryHistory windowRead ∧ UnaryHistory sourceRead ∧
                          UnaryHistory toleranceRead ∧ UnaryHistory meetRead ∧
                            UnaryHistory completionRead ∧ Cont index windows windowRead ∧
                              Cont windowRead tail sourceRead ∧
                                Cont modulus tolerance toleranceRead ∧
                                  Cont toleranceRead tail meetRead ∧
                                    Cont meetRead sealRow completionRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle sourceRead pkg ∧
                                          PkgSig bundle toleranceRead pkg ∧
                                            PkgSig bundle meetRead pkg ∧
                                              PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowsRead windowTailRead modulusToleranceRead toleranceTailRead
    meetSealRead sourcePkg tolerancePkg meetPkg completionPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
      _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance,
        namePkg⟩ := packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsRead
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed windowReadUnary tailUnary windowTailRead
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceRead
  have meetReadUnary : UnaryHistory meetRead :=
    unary_cont_closed toleranceReadUnary tailUnary toleranceTailRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed meetReadUnary sealRowUnary meetSealRead
  exact
    ⟨windowReadUnary, sourceReadUnary, toleranceReadUnary, meetReadUnary,
      completionReadUnary, indexWindowsRead, windowTailRead, modulusToleranceRead,
      toleranceTailRead, meetSealRead, namePkg, sourcePkg, tolerancePkg, meetPkg,
      completionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
