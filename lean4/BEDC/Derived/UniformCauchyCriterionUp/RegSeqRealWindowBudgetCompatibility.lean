import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_regseq_real_window_budget_compatibility [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name thresholdRead
      tailRead sealRead sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index windows thresholdRead →
        Cont tolerance tail tailRead →
          Cont tail sealRow sealRead →
            Cont sealRead tail sharedRead →
              PkgSig bundle tailRead pkg →
                PkgSig bundle sealRead pkg →
                  PkgSig bundle sharedRead pkg →
                    UnaryHistory thresholdRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory sharedRead ∧
                        Cont index windows thresholdRead ∧ Cont tolerance tail tailRead ∧
                          Cont tail sealRow sealRead ∧ Cont sealRead tail sharedRead ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle sharedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowsThreshold toleranceTailRead tailSealRead sealTailShared _tailReadPkg
    _sealReadPkg sharedReadPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsThreshold
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed toleranceUnary tailUnary toleranceTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed sealReadUnary tailUnary sealTailShared
  exact
    ⟨thresholdUnary, tailReadUnary, sealReadUnary, sharedReadUnary, indexWindowsThreshold,
      toleranceTailRead, tailSealRead, sealTailShared, namePkg, sharedReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
