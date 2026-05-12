import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyLimitSealPacket [AskSetup] [PackageSetup]
    (source schedule dyadic diagonal sealRow transportRow provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory dyadic ∧
    UnaryHistory diagonal ∧ UnaryHistory sealRow ∧ UnaryHistory transportRow ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont source schedule dyadic ∧
        Cont dyadic diagonal sealRow ∧ Cont sealRow transportRow provenance ∧
          Cont provenance nameRow nameRow ∧ Cont diagonal transportRow sealRow ∧
            PkgSig bundle nameRow pkg

theorem CauchyLimitSealPacket_namecert_obligations [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealPacket source schedule dyadic diagonal sealRow transportRow provenance
        nameRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row nameRow ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => Cont provenance nameRow row ∧ UnaryHistory source ∧
          UnaryHistory schedule)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont diagonal transportRow sealRow)
        (fun row row' : BHist => hsame row row') := by
  intro packet
  obtain ⟨sourceUnary, scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, nameUnary, _sourceScheduleRow, _sealRow,
    _provenanceRow, nameRoute, diagonalTransportRow, namePkg⟩ := packet
  exact {
    core := {
      carrier_inhabited := ⟨nameRow, hsame_refl nameRow, nameUnary, namePkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      obtain ⟨sameName, _rowUnary, _rowPkg⟩ := sourceRow
      cases sameName
      exact ⟨nameRoute, sourceUnary, scheduleUnary⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, diagonalTransportRow⟩
  }

end BEDC.Derived.CauchyLimitSealUp
