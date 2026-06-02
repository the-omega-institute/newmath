import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SignedDyadicExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SignedDyadicExpansionCarrier [AskSetup] [PackageSetup]
    (S W E T F A R L H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory E ∧ UnaryHistory T ∧
    UnaryHistory F ∧ UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory L ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont S W E ∧ Cont T F A ∧ Cont A R L ∧ PkgSig bundle P pkg

theorem SignedDyadicExpansionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S W E T F A R L H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDyadicExpansionCarrier S W E T F A R L H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧ SignedDyadicExpansionCarrier S W E T F A R L H C P N bundle pkg)
        (fun row : BHist =>
          hsame row N ∧ Cont S W E ∧ Cont T F A ∧ Cont A R L)
        (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier
  have carrierData :
      SignedDyadicExpansionCarrier S W E T F A R L H C P N bundle pkg :=
    carrier
  obtain ⟨_sUnary, _wUnary, _eUnary, _tUnary, _fUnary, _aUnary, _rUnary,
    _lUnary, _hUnary, _cUnary, _pUnary, _nUnary, sweRoute, tfaRoute, arlRoute,
    provenancePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, carrierData⟩
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
      exact ⟨source.left, sweRoute, tfaRoute, arlRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }

end BEDC.Derived.SignedDyadicExpansionUp
