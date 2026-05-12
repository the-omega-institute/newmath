import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionMonadPacket [AskSetup] [PackageSetup]
    (sourceFamily windows observations schedule diagonal sealRow transport route nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceFamily ∧ UnaryHistory windows ∧ UnaryHistory schedule ∧
    UnaryHistory diagonal ∧ UnaryHistory transport ∧ UnaryHistory nameRow ∧
      Cont schedule windows observations ∧ Cont observations diagonal sealRow ∧
        Cont sealRow transport route ∧ Cont route nameRow sealRow ∧
          PkgSig bundle sealRow pkg

theorem CauchyCompletionMonadPacket_namecert_obligations [AskSetup] [PackageSetup]
    {sourceFamily windows observations schedule diagonal sealRow transport route nameRow :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMonadPacket sourceFamily windows observations schedule diagonal sealRow
        transport route nameRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row sealRow ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => Cont schedule windows observations ∧
          Cont observations diagonal row)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont observations diagonal row)
        (fun row row' : BHist => hsame row row') := by
  intro packet
  obtain ⟨_sourceFamilyUnary, windowsUnary, scheduleUnary, diagonalUnary, _transportUnary,
    _nameRowUnary, scheduleWindowsObservations, observationsDiagonalSealRow,
    _sealRowTransportRoute, _routeNameSealRow, sealRowPkg⟩ := packet
  have observationsUnary : UnaryHistory observations :=
    unary_cont_closed scheduleUnary windowsUnary scheduleWindowsObservations
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed observationsUnary diagonalUnary observationsDiagonalSealRow
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRow ⟨hsame_refl sealRow, sealRowUnary, sealRowPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨scheduleWindowsObservations,
          cont_result_hsame_transport observationsDiagonalSealRow
            (hsame_symm sourceRow.left)⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right.right,
          cont_result_hsame_transport observationsDiagonalSealRow
            (hsame_symm sourceRow.left)⟩
  }

end BEDC.Derived.CauchyCompletionMonadUp
