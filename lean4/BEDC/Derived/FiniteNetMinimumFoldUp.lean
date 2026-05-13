import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteNetMinimumFoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteNetMinimumFoldPacket [AskSetup] [PackageSetup]
    (probeRow radiusRow accumulator lowerBound transportRow provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory probeRow ∧ UnaryHistory radiusRow ∧ UnaryHistory accumulator ∧
    UnaryHistory lowerBound ∧ UnaryHistory nameRow ∧
      Cont probeRow radiusRow accumulator ∧ Cont accumulator lowerBound transportRow ∧
        Cont transportRow nameRow provenance ∧ PkgSig bundle provenance pkg

theorem FiniteNetMinimumFoldPacket_namecert_obligations [AskSetup] [PackageSetup]
    {probeRow radiusRow accumulator lowerBound transportRow provenance nameRow exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket probeRow radiusRow accumulator lowerBound transportRow
        provenance nameRow bundle pkg →
      Cont accumulator lowerBound exported →
        PkgSig bundle exported pkg →
          SemanticNameCert
            (fun row : BHist => hsame row exported ∧ UnaryHistory row ∧
              PkgSig bundle row pkg)
            (fun row : BHist => Cont accumulator lowerBound row ∧
              Cont probeRow radiusRow accumulator)
            (fun row : BHist => PkgSig bundle row pkg ∧
              Cont transportRow nameRow provenance)
            (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro packet exportRoute exportPkg
  obtain ⟨probeUnary, radiusUnary, accumulatorUnary, lowerBoundUnary, _nameRowUnary,
    probeRadiusAccumulator, _accumulatorLowerTransport, transportNameProvenance,
    _provenancePkg⟩ := packet
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed accumulatorUnary lowerBoundUnary exportRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary, exportPkg⟩
      equiv_refl := by
        intro row _source
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
        ⟨cont_result_hsame_transport exportRoute (hsame_symm sourceRow.left),
          probeRadiusAccumulator⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, transportNameProvenance⟩
  }

end BEDC.Derived.FiniteNetMinimumFoldUp
