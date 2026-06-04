import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedCauchyFilterBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedCauchyFilterBasisCarrier [AskSetup] [PackageSetup]
    (B L S R D W T E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory B ∧ UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory R ∧
    UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory T ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont B L S ∧ Cont S R D ∧ Cont D W T ∧ Cont T E C ∧
          PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem LocatedCauchyFilterBasisCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B L S R D W T E H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧ LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N
              bundle pkg)
          (fun row : BHist => hsame row N ∧ Cont B L S ∧ Cont S R D ∧ Cont D W T)
          (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory B ∧ UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory R ∧
          UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory T ∧ UnaryHistory E ∧
            Cont B L S ∧ Cont S R D ∧ Cont D W T ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨bUnary, lUnary, sUnary, rUnary, dUnary, wUnary, tUnary, eUnary,
    hUnary, cUnary, pUnary, nUnary, basisLocated, windowReadback, toleranceWitness,
    tailSeal, provenancePkg, namePkg⟩ := carrier
  have carrierRows :
      LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N bundle pkg :=
    ⟨bUnary, lUnary, sUnary, rUnary, dUnary, wUnary, tUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, basisLocated, windowReadback, toleranceWitness,
      tailSeal, provenancePkg, namePkg⟩
  have sourceName :
      (fun row : BHist =>
        hsame row N ∧ LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N
          bundle pkg) N := by
    exact ⟨hsame_refl N, carrierRows⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row N ∧ LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N
            bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro N sourceName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧ LocatedCauchyFilterBasisCarrier B L S R D W T E H C P N
              bundle pkg)
          (fun row : BHist => hsame row N ∧ Cont B L S ∧ Cont S R D ∧ Cont D W T)
          (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact ⟨source.left, basisLocated, windowReadback, toleranceWitness⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, provenancePkg, namePkg⟩
    }
  exact
    ⟨cert, bUnary, lUnary, sUnary, rUnary, dUnary, wUnary, tUnary, eUnary,
      basisLocated, windowReadback, toleranceWitness, provenancePkg, namePkg⟩

end BEDC.Derived.LocatedCauchyFilterBasisUp
