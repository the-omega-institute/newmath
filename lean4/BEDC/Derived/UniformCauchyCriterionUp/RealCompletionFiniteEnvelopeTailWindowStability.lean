import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_completion_finite_envelope_tail_window_stability
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      regseqRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index windows windowRead →
        Cont windowRead tail regseqRead →
          Cont regseqRead sealRow completionRead →
            PkgSig bundle completionRead pkg →
              UnaryHistory windows ∧ UnaryHistory windowRead ∧ UnaryHistory regseqRead ∧
                UnaryHistory completionRead ∧ Cont index windows modulus ∧
                  Cont index windows windowRead ∧ Cont windowRead tail regseqRead ∧
                    Cont regseqRead sealRow completionRead ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowsWindow windowTailRegseq regseqSealCompletion completionPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsWindow
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed windowReadUnary tailUnary windowTailRegseq
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed regseqReadUnary sealRowUnary regseqSealCompletion
  exact
    ⟨windowsUnary, windowReadUnary, regseqReadUnary, completionReadUnary,
      indexWindowsModulus, indexWindowsWindow, windowTailRegseq, regseqSealCompletion, namePkg,
      completionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
