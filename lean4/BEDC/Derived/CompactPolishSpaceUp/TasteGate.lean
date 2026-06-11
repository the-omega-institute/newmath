import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactPolishSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactPolishSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K P C S W R H T Q N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ∧ UnaryHistory P ∧ UnaryHistory C ∧ UnaryHistory S ∧
      UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory T ∧
        UnaryHistory Q ∧ UnaryHistory N ∧ Cont K W T ∧ Cont P C T ∧
          Cont S R T ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg →
      SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧ UnaryHistory K ∧ UnaryHistory P ∧ UnaryHistory C ∧
            UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory H ∧
              UnaryHistory T ∧ UnaryHistory Q ∧ UnaryHistory N ∧ Cont K W T ∧
                Cont P C T ∧ Cont S R T ∧ PkgSig bundle Q pkg ∧
                  PkgSig bundle N pkg)
        (fun row : BHist =>
          hsame row N ∧ Cont K W T ∧ Cont P C T ∧ Cont S R T)
        (fun row : BHist =>
          hsame row N ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro obligations
  obtain ⟨hK, hP, hC, hS, hW, hR, hH, hT, hQ, hN, hKW, hPC, hSR, hQpkg,
    hNpkg⟩ := obligations
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro N
          ⟨hsame_refl N, hK, hP, hC, hS, hW, hR, hH, hT, hQ, hN, hKW, hPC,
            hSR, hQpkg, hNpkg⟩
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      obtain ⟨same, _hK, _hP, _hC, _hS, _hW, _hR, _hH, _hT, _hQ, _hN, hKW,
        hPC, hSR, _hQpkg, _hNpkg⟩ := source
      exact ⟨same, hKW, hPC, hSR⟩
    ledger_sound := by
      intro _row source
      obtain ⟨same, _hK, _hP, _hC, _hS, _hW, _hR, _hH, _hT, _hQ, _hN, _hKW,
        _hPC, _hSR, hQpkg, hNpkg⟩ := source
      exact ⟨same, hQpkg, hNpkg⟩
  }

end BEDC.Derived.CompactPolishSpaceUp
