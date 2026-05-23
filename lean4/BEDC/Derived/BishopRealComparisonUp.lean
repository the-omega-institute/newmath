import BEDC.Derived.BishopRealComparisonUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRealComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopRealComparisonPacket [AskSetup] [PackageSetup]
    (bishop completion located cut realSeal readback transports provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig UnaryHistory NameCert
  UnaryHistory bishop ∧ UnaryHistory completion ∧ UnaryHistory located ∧ UnaryHistory cut ∧
    UnaryHistory realSeal ∧ UnaryHistory readback ∧ UnaryHistory transports ∧
      UnaryHistory provenance ∧ UnaryHistory localCert ∧ PkgSig bundle provenance pkg

theorem BishopRealComparisonPacket_namecert_obligations [AskSetup] [PackageSetup]
    {bishop completion located cut realSeal readback transports provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRealComparisonPacket bishop completion located cut realSeal readback transports provenance
        localCert bundle pkg ->
      Cont realSeal readback consumer ->
        PkgSig bundle consumer pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row localCert ∧
                  BishopRealComparisonPacket bishop completion located cut realSeal readback
                    transports provenance localCert bundle pkg)
              (fun row : BHist => hsame row localCert)
              (fun row : BHist => hsame row localCert ∧ PkgSig bundle consumer pkg)
              hsame ∧
            UnaryHistory bishop ∧ UnaryHistory completion ∧ UnaryHistory located ∧
              UnaryHistory cut ∧ UnaryHistory realSeal ∧ UnaryHistory consumer ∧
                Cont realSeal readback consumer ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig UnaryHistory SemanticNameCert
  intro packet sealReadback consumerPkg
  have packetWitness := packet
  obtain ⟨bishopUnary, completionUnary, locatedUnary, cutUnary, realSealUnary, readbackUnary,
    _transportsUnary, _provenanceUnary, _localCertUnary, provenancePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed realSealUnary readbackUnary sealReadback
  have sourceAtLocal :
      hsame localCert localCert ∧
        BishopRealComparisonPacket bishop completion located cut realSeal readback transports
          provenance localCert bundle pkg :=
    ⟨hsame_refl localCert, packetWitness⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localCert ∧
              BishopRealComparisonPacket bishop completion located cut realSeal readback transports
                provenance localCert bundle pkg)
          (fun row : BHist => hsame row localCert)
          (fun row : BHist => hsame row localCert ∧ PkgSig bundle consumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localCert sourceAtLocal
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
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }
  exact
    ⟨cert, bishopUnary, completionUnary, locatedUnary, cutUnary, realSealUnary, consumerUnary,
      sealReadback, provenancePkg, consumerPkg⟩

end BEDC.Derived.BishopRealComparisonUp
