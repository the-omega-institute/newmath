import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyInterpolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyInterpolationNameCertObligations [AskSetup] [PackageSetup]
    {R D M W S E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R -> UnaryHistory D -> UnaryHistory M -> UnaryHistory W ->
      UnaryHistory S -> UnaryHistory E -> UnaryHistory H -> UnaryHistory C ->
        UnaryHistory P -> UnaryHistory N -> Cont R D M -> Cont M W S ->
          Cont S E C -> PkgSig bundle P pkg -> PkgSig bundle N pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row R ∨ hsame row D ∨ hsame row M ∨ hsame row W ∨
                  hsame row S ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _rUnary _dUnary _mUnary _wUnary _sUnary _eUnary _hUnary _cUnary _pUnary
    nUnary _sourceMesh _meshWindow _scheduleSeal _provenancePkg namePkg
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namePkg⟩
  }

end BEDC.Derived.RegularCauchyInterpolationUp
