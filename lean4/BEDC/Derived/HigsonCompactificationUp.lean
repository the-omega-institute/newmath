import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HigsonCompactificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HigsonCompactificationCarrier [AskSetup] [PackageSetup]
    (U M A C F R S B H T P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory C ∧
    UnaryHistory F ∧ UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory B ∧
      UnaryHistory H ∧ UnaryHistory T ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem HigsonCompactificationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {U M A C F R S B H T P N observation : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HigsonCompactificationCarrier U M A C F R S B H T P N bundle pkg →
      Cont M A observation →
        PkgSig bundle observation pkg →
          SemanticNameCert
              (fun row : BHist => hsame row observation ∧ UnaryHistory row)
              (fun row : BHist => hsame row observation)
              (fun row : BHist => hsame row observation ∧ PkgSig bundle observation pkg)
              hsame ∧
            UnaryHistory observation := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier metricAlgebraRoute observationPkg
  obtain ⟨_uUnary, mUnary, aUnary, _cUnary, _fUnary, _rUnary, _sUnary, _bUnary,
    _hUnary, _tUnary, _pUnary, _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed mUnary aUnary metricAlgebraRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row observation ∧ UnaryHistory row)
          (fun row : BHist => hsame row observation)
          (fun row : BHist => hsame row observation ∧ PkgSig bundle observation pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro observation
        ⟨hsame_refl observation, observationUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, observationPkg⟩
  }
  exact ⟨cert, observationUnary⟩

end BEDC.Derived.HigsonCompactificationUp
