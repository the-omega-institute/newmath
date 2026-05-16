import BEDC.Derived.PhysicalModelAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PhysicalModelAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PhysicalModelAuditPacket [AskSetup] [PackageSetup]
    (Q R O M C T Y D L F S H U P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory Q ∧ UnaryHistory R ∧ UnaryHistory O ∧ UnaryHistory M ∧
    UnaryHistory C ∧ UnaryHistory T ∧ UnaryHistory Y ∧ UnaryHistory D ∧
      UnaryHistory L ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory H ∧
        UnaryHistory U ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont Q R O ∧
          Cont O M C ∧ Cont T Y D ∧ Cont L F S ∧ Cont H U P ∧
            Cont U P N ∧ PkgSig bundle N pkg

theorem PhysicalModelAuditPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {Q R O M C T Y D L F S H U P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PhysicalModelAuditPacket Q R O M C T Y D L F S H U P N bundle pkg →
      SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => Cont U P row ∧ Cont Q R O ∧ Cont O M C)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont T Y D ∧ Cont L F S)
        (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet
  obtain ⟨_QUnary, _RUnary, _OUnary, _MUnary, _CUnary, _TUnary, _YUnary, _DUnary,
    _LUnary, _FUnary, _SUnary, _HUnary, _UUnary, _PUnary, NUnary, QRO, OMC, TYD,
    LFS, _HUP, UPN, NPkg⟩ := packet
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, NUnary, NPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _row' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left
      exact ⟨UPN, QRO, OMC⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, TYD, LFS⟩
  }

end BEDC.Derived.PhysicalModelAuditUp
