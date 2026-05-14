import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_tail_meet_root_export [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailMeet
      rootExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont modulus tolerance tailMeet →
        Cont tailMeet sealRow rootExport →
          PkgSig bundle rootExport pkg →
            UnaryHistory modulus ∧ UnaryHistory tolerance ∧ UnaryHistory tailMeet ∧
              UnaryHistory sealRow ∧ UnaryHistory rootExport ∧ hsame tail tailMeet ∧
                Cont modulus tolerance tailMeet ∧ Cont tailMeet sealRow rootExport ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle rootExport pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet modulusToleranceTailMeet tailMeetSealRootExport rootExportPkg
  obtain ⟨_indexUnary, _windowsUnary, modulusUnary, toleranceUnary, _tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have tailMeetUnary : UnaryHistory tailMeet :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceTailMeet
  have rootExportUnary : UnaryHistory rootExport :=
    unary_cont_closed tailMeetUnary sealRowUnary tailMeetSealRootExport
  have sameTailMeet : hsame tail tailMeet :=
    cont_respects_hsame (hsame_refl modulus) (hsame_refl tolerance) modulusToleranceTail
      modulusToleranceTailMeet
  exact
    ⟨modulusUnary, toleranceUnary, tailMeetUnary, sealRowUnary, rootExportUnary,
      sameTailMeet, modulusToleranceTailMeet, tailMeetSealRootExport, namePkg, rootExportPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
