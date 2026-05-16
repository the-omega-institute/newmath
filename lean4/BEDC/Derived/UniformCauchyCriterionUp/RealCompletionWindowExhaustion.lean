import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_completion_window_exhaustion
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name
      windowRead tailRead sealRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index windows windowRead →
        Cont windowRead tail tailRead →
          Cont tail sealRow sealRead →
            Cont tailRead sealRead completionRead →
              PkgSig bundle tailRead pkg →
                PkgSig bundle sealRead pkg →
                  PkgSig bundle completionRead pkg →
                    UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                      UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                        UnaryHistory windowRead ∧ UnaryHistory tailRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory completionRead ∧
                            Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                              Cont index windows windowRead ∧ Cont windowRead tail tailRead ∧
                                Cont tail sealRow sealRead ∧
                                  Cont tailRead sealRead completionRead ∧
                                    PkgSig bundle name pkg ∧ PkgSig bundle tailRead pkg ∧
                                      PkgSig bundle sealRead pkg ∧
                                        PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowsRead windowTailRead tailSealRead tailSealCompletion tailReadPkg
    sealReadPkg completionPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsRead
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed windowReadUnary tailUnary windowTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed tailReadUnary sealReadUnary tailSealCompletion
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      windowReadUnary, tailReadUnary, sealReadUnary, completionReadUnary, indexWindowsModulus,
      modulusToleranceTail, indexWindowsRead, windowTailRead, tailSealRead, tailSealCompletion,
      namePkg, tailReadPkg, sealReadPkg, completionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
