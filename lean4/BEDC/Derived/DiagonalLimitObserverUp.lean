import BEDC.Derived.DiagonalLimitObserverUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core

namespace BEDC.Derived.DiagonalLimitObserverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem DiagonalLimitObserver_namecert_obligations [AskSetup] [PackageSetup]
    {D W Q T S R H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle R pkg →
      hsame N R →
        SemanticNameCert
          (fun row : BHist =>
            hsame row R ∧
              ∃ packet : DiagonalLimitObserverUp,
                FieldFaithful.fields packet = [D, W, Q, T, S, R, H, C, P, N])
          (fun row : BHist => hsame row R)
          (fun row : BHist => hsame row R ∧ PkgSig bundle R pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame
  intro pkgSig _sameName
  let packet : DiagonalLimitObserverUp := DiagonalLimitObserverUp.mk D W Q T S R H C P N
  have packetFields :
      FieldFaithful.fields packet = [D, W, Q, T, S, R, H, C, P, N] := by
    rfl
  have sourceR :
      (fun row : BHist =>
        hsame row R ∧
          ∃ packet : DiagonalLimitObserverUp,
            FieldFaithful.fields packet = [D, W, Q, T, S, R, H, C, P, N]) R := by
    exact And.intro (hsame_refl R) ⟨packet, packetFields⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro R sourceR
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact And.intro source.left pkgSig
  }

end BEDC.Derived.DiagonalLimitObserverUp
