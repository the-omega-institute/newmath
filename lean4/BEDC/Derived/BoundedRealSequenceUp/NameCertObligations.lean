import BEDC.Derived.BoundedRealSequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedRealSequenceUp.NameCertObligations

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedRealSequenceCarrier [AskSetup] [PackageSetup]
    (source windows readback realSeal interval transport replay provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  UnaryHistory source ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
    UnaryHistory realSeal ∧ UnaryHistory interval ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont readback realSeal interval ∧ hsame transport provenance ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg

theorem BoundedRealSequenceCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {source windows readback realSeal interval transport replay provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedRealSequenceCarrier source windows readback realSeal interval transport replay
        provenance localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              BoundedRealSequenceCarrier source windows readback realSeal interval transport
                replay provenance localCert bundle pkg)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory source ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
          Cont readback realSeal interval ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier
  have carrierPacket :
      BoundedRealSequenceCarrier source windows readback realSeal interval transport replay
        provenance localCert bundle pkg :=
    carrier
  obtain ⟨sourceUnary, _windowsUnary, readbackUnary, realSealUnary, _intervalUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, intervalRoute,
    _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              BoundedRealSequenceCarrier source windows readback realSeal interval transport
                replay provenance localCert bundle pkg)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro provenance ⟨hsame_refl provenance, carrierPacket⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact sourceRow.left
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, provenancePkg⟩
    }
  exact ⟨cert, sourceUnary, readbackUnary, realSealUnary, intervalRoute, provenancePkg⟩

end BEDC.Derived.BoundedRealSequenceUp.NameCertObligations
