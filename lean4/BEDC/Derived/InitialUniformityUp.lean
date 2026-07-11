import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def InitialUniformityUp [AskSetup] [PackageSetup]
    (source target map entourage transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory map ∧
    UnaryHistory entourage ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont source map entourage ∧
        Cont target entourage replay ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

namespace InitialUniformityUp

theorem InitialUniformityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source target map entourage transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.InitialUniformityUp source target map entourage transport replay provenance
        localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            BEDC.Derived.InitialUniformityUp source target map entourage transport replay
              provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist =>
            BEDC.Derived.InitialUniformityUp source target map entourage transport replay
              provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist =>
            BEDC.Derived.InitialUniformityUp source target map entourage transport replay
              provenance localName bundle pkg ∧ hsame row localName)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            BEDC.Derived.InitialUniformityUp source target map entourage transport replay
              provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist =>
            BEDC.Derived.InitialUniformityUp source target map entourage transport replay
              provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist =>
            BEDC.Derived.InitialUniformityUp source target map entourage transport replay
              provenance localName bundle pkg ∧ hsame row localName)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨carrier, hsame_refl localName⟩
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
        intro _row _other sameRows sourceData
        exact ⟨sourceData.left, hsame_trans (hsame_symm sameRows) sourceData.right⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact sourceData
    ledger_sound := by
      intro _row sourceData
      exact sourceData
  }
  exact cert

end InitialUniformityUp
end BEDC.Derived
