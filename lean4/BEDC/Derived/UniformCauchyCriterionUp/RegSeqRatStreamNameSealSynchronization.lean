import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_regseqrat_streamname_seal_synchronization
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name streamRead
      regRead sealSync terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows tail streamRead ->
        Cont streamRead tolerance regRead ->
          Cont regRead sealRow sealSync ->
            Cont sealSync sealRow terminal ->
              PkgSig bundle terminal pkg ->
                UnaryHistory streamRead ∧ UnaryHistory regRead ∧ UnaryHistory sealSync ∧
                  UnaryHistory terminal ∧ Cont windows tail streamRead ∧
                    Cont streamRead tolerance regRead ∧ Cont regRead sealRow sealSync ∧
                      Cont sealSync sealRow terminal ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsTailStream streamToleranceReg regSealSync syncSealTerminal terminalPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealTransports, _transportsRoutesProvenance, namePkg⟩ :=
      packet
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowsUnary tailUnary windowsTailStream
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed streamUnary toleranceUnary streamToleranceReg
  have sealSyncUnary : UnaryHistory sealSync :=
    unary_cont_closed regUnary sealRowUnary regSealSync
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealSyncUnary sealRowUnary syncSealTerminal
  exact
    ⟨streamUnary, regUnary, sealSyncUnary, terminalUnary, windowsTailStream,
      streamToleranceReg, regSealSync, syncSealTerminal, namePkg, terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
