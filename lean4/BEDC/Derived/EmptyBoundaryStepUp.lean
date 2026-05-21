import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Ext
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.EmptyBoundaryStepUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def EmptyBoundaryStepCarrier [AskSetup] [PackageSetup]
    (source : BHist) (mark : BMark)
    (result transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Ext source mark result ∧ Cont source route result ∧ hsame transport transport ∧
    hsame nameCert nameCert ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg

theorem EmptyBoundaryStepCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source result transport route provenance nameCert : BHist} {mark : BMark}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EmptyBoundaryStepCarrier source mark result transport route provenance nameCert bundle pkg ->
      Ext source mark result /\
        SemanticNameCert
          (fun row : BHist => hsame row nameCert)
          (fun row : BHist => hsame row source \/ hsame row result \/ hsame row nameCert)
          (fun row : BHist =>
            PkgSig bundle provenance pkg /\ PkgSig bundle nameCert pkg /\ hsame row nameCert)
          hsame /\
          Cont source route result /\ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨extStep, contRoute, _transportSelf, _nameCertSelf, provenancePkg, nameCertPkg⟩ :=
    carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameCert)
          (fun row : BHist => hsame row source \/ hsame row result \/ hsame row nameCert)
          (fun row : BHist =>
            PkgSig bundle provenance pkg /\ PkgSig bundle nameCert pkg /\ hsame row nameCert)
          hsame := by
    exact
      { core :=
          { carrier_inhabited := Exists.intro nameCert (hsame_refl nameCert)
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
              exact hsame_trans (hsame_symm sameRows) sourceRow }
        pattern_sound := by
          intro _row sourceRow
          exact Or.inr (Or.inr sourceRow)
        ledger_sound := by
          intro _row sourceRow
          exact ⟨provenancePkg, nameCertPkg, sourceRow⟩ }
  exact ⟨extStep, cert, contRoute, nameCertPkg⟩

end BEDC.Derived.EmptyBoundaryStepUp
