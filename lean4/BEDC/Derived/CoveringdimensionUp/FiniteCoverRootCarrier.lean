import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoveringDimensionFiniteCoverRootCarrier [AskSetup] [PackageSetup]
    (K C A M D Q G H T P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory K ∧ UnaryHistory C ∧ UnaryHistory A ∧ UnaryHistory M ∧
    UnaryHistory D ∧ UnaryHistory Q ∧ UnaryHistory G ∧ UnaryHistory H ∧
      UnaryHistory T ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CoveringDimensionFiniteCoverRootCarrier_empty_admission [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteCoverRootCarrier BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row BHist.Empty ∧
              CoveringDimensionFiniteCoverRootCarrier BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty bundle pkg)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle row pkg ∨ PkgSig bundle BHist.Empty pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier
  have carrierSource := carrier
  obtain ⟨KUnary, _CUnary, _AUnary, _MUnary, _DUnary, _QUnary, _GUnary, _HUnary,
    _TUnary, provenancePkg, _localNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro BHist.Empty ⟨hsame_refl BHist.Empty, carrierSource⟩
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
        intro row other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro row source
      exact unary_transport KUnary (hsame_symm source.left)
    ledger_sound := by
      intro _row source
      cases source.left
      exact Or.inl provenancePkg
  }

end BEDC.Derived.CoveringdimensionUp
