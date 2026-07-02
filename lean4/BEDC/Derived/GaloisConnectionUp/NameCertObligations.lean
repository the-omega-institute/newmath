import BEDC.Derived.GaloisConnectionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GaloisConnectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GaloisConnectionCarrier [AskSetup] [PackageSetup]
    (P Q F G M A T R L N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory P ∧ UnaryHistory Q ∧ UnaryHistory F ∧ UnaryHistory G ∧
    UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory T ∧ UnaryHistory R ∧
      UnaryHistory L ∧ UnaryHistory N ∧ PkgSig bundle L pkg ∧ PkgSig bundle N pkg

theorem GaloisConnectionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {P Q F G M A T R L N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisConnectionCarrier P Q F G M A T R L N bundle pkg ->
      PkgSig bundle N pkg ->
        SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row Q ∨ hsame row F ∨ hsame row G ∨ hsame row M ∨
              hsame row A ∨ hsame row T ∨ hsame row R ∨ hsame row L ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier namePkg
  obtain ⟨_pUnary, _qUnary, _fUnary, _gUnary, _mUnary, _aUnary, _tUnary, _rUnary,
    _lUnary, nUnary, _provenancePkg, _carrierNamePkg⟩ := carrier
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namePkg⟩
  }

end BEDC.Derived.GaloisConnectionUp
