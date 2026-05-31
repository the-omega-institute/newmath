import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicMetricTriangleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicMetricTriangleCarrier [AskSetup] [PackageSetup]
    (x y z dxy dyz dxz a b t h c p n : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory z ∧
    UnaryHistory dxy ∧ UnaryHistory dyz ∧ UnaryHistory dxz ∧
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory t ∧ UnaryHistory h ∧
        UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
          Cont dxz dxy b ∧ Cont b t c ∧ PkgSig bundle p pkg

theorem DyadicMetricTriangleCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {x y z dxy dyz dxz a b t h c p n : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMetricTriangleCarrier x y z dxy dyz dxz a b t h c p n bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row b ∧
              DyadicMetricTriangleCarrier x y z dxy dyz dxz a b t h c p n bundle pkg)
          (fun row : BHist =>
            hsame row b ∧ UnaryHistory dxz ∧ UnaryHistory dxy ∧ UnaryHistory dyz)
          (fun row : BHist => hsame row b ∧ PkgSig bundle p pkg)
          hsame ∧
        UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory z ∧
          UnaryHistory dxy ∧ UnaryHistory dyz ∧ UnaryHistory dxz ∧
            UnaryHistory a ∧ UnaryHistory b ∧ Cont dxz dxy b ∧
              Cont b t c ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨xUnary, yUnary, zUnary, dxyUnary, dyzUnary, dxzUnary, aUnary, bUnary,
    tUnary, hUnary, cUnary, pUnary, nUnary, triangleRoute, handoffRoute,
    provenancePkg⟩ := carrier
  have carrierWitness :
      DyadicMetricTriangleCarrier x y z dxy dyz dxz a b t h c p n bundle pkg :=
    ⟨xUnary, yUnary, zUnary, dxyUnary, dyzUnary, dxzUnary, aUnary, bUnary,
      tUnary, hUnary, cUnary, pUnary, nUnary, triangleRoute, handoffRoute,
      provenancePkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row b ∧
              DyadicMetricTriangleCarrier x y z dxy dyz dxz a b t h c p n bundle pkg)
          (fun row : BHist =>
            hsame row b ∧ UnaryHistory dxz ∧ UnaryHistory dxy ∧ UnaryHistory dyz)
          (fun row : BHist => hsame row b ∧ PkgSig bundle p pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨b, hsame_refl b, carrierWitness⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        obtain ⟨sameRowB, sourceCarrier⟩ := source
        exact ⟨hsame_trans (hsame_symm sameRows) sameRowB, sourceCarrier⟩
    }
    pattern_sound := by
      intro row source
      obtain ⟨sameRowB, _sourceCarrier⟩ := source
      exact ⟨sameRowB, dxzUnary, dxyUnary, dyzUnary⟩
    ledger_sound := by
      intro row source
      obtain ⟨sameRowB, _sourceCarrier⟩ := source
      exact ⟨sameRowB, provenancePkg⟩
  }
  exact
    ⟨cert, xUnary, yUnary, zUnary, dxyUnary, dyzUnary, dxzUnary, aUnary,
      bUnary, triangleRoute, handoffRoute, provenancePkg⟩

end BEDC.Derived.DyadicMetricTriangleUp
