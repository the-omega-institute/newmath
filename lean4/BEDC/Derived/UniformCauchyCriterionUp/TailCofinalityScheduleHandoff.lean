import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_tail_cofinality_schedule_handoff
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name scheduleRead
      sealRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail scheduleRead →
        Cont scheduleRead sealRow sealRead →
          Cont sealRead name completionRead →
            PkgSig bundle scheduleRead pkg →
              PkgSig bundle sealRead pkg →
                PkgSig bundle completionRead pkg →
                  UnaryHistory scheduleRead ∧ UnaryHistory sealRead ∧
                    UnaryHistory completionRead ∧ Cont index tail scheduleRead ∧
                      Cont scheduleRead sealRow sealRead ∧
                        Cont sealRead name completionRead ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle completionRead pkg ∧
                            (Cont scheduleRead (BHist.e0 tail) index → False) ∧
                              (Cont scheduleRead (BHist.e1 tail) index → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailSchedule scheduleSealRead sealNameCompletion _schedulePkg _sealPkg
    completionPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed indexUnary tailUnary indexTailSchedule
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed scheduleUnary sealRowUnary scheduleSealRead
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealReadUnary nameUnary sealNameCompletion
  exact
    ⟨scheduleUnary, sealReadUnary, completionUnary, indexTailSchedule, scheduleSealRead,
      sealNameCompletion, namePkg, completionPkg,
      (fun backToIndex =>
        cont_mutual_extension_right_tail_absurd.left indexTailSchedule backToIndex),
      (fun backToIndex =>
        cont_mutual_extension_right_tail_absurd.right indexTailSchedule backToIndex)⟩

end BEDC.Derived.UniformCauchyCriterionUp
