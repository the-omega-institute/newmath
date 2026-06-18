import BEDC.Derived.EgorovUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EgorovUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EgorovCarrier [AskSetup] [PackageSetup]
    (measure prob family limit schedule readback exceptional window uniformity ledger transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  (∃ packet : EgorovUp,
      packet =
        EgorovUp.mk measure prob family limit schedule readback exceptional window uniformity ledger
          transport replay provenance localName) ∧
    UnaryHistory measure ∧ UnaryHistory prob ∧ UnaryHistory family ∧ UnaryHistory limit ∧
      UnaryHistory schedule ∧ UnaryHistory readback ∧ UnaryHistory exceptional ∧
        UnaryHistory window ∧ UnaryHistory uniformity ∧ UnaryHistory ledger ∧
          UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
            UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem EgorovCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {measure prob family limit schedule readback exceptional window uniformity ledger transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EgorovCarrier measure prob family limit schedule readback exceptional window uniformity ledger
        transport replay provenance localName bundle pkg ->
      Cont exceptional window uniformity ->
        Cont uniformity ledger replay ->
          PkgSig bundle provenance pkg ->
            SemanticNameCert
                  (fun row : BHist => hsame row uniformity ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row exceptional ∨ hsame row window ∨ hsame row uniformity ∨
                      hsame row ledger)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont exceptional window uniformity ∧
                      Cont uniformity ledger replay ∧ PkgSig bundle provenance pkg)
                  hsame ∧
              UnaryHistory exceptional ∧ UnaryHistory window ∧ UnaryHistory uniformity ∧
                UnaryHistory ledger := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier exceptionalWindowRoute uniformityLedgerRoute provenancePkg
  obtain ⟨_packetWitness, _measureUnary, _probUnary, _familyUnary, _limitUnary,
    _scheduleUnary, _readbackUnary, exceptionalUnary, windowUnary, uniformityUnary,
    ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkgCarrier, _localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformity ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row exceptional ∨ hsame row window ∨ hsame row uniformity ∨
              hsame row ledger)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont exceptional window uniformity ∧
              Cont uniformity ledger replay ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformity ⟨hsame_refl uniformity, uniformityUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, exceptionalWindowRoute, uniformityLedgerRoute, provenancePkg⟩
  }
  exact ⟨cert, exceptionalUnary, windowUnary, uniformityUnary, ledgerUnary⟩

end BEDC.Derived.EgorovUp
