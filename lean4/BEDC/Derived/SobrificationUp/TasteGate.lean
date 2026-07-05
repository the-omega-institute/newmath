import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SobrificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SobrificationCarrier [AskSetup] [PackageSetup]
    (T I Sigma preorder G H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory T ∧ UnaryHistory I ∧ UnaryHistory Sigma ∧ UnaryHistory preorder ∧
    UnaryHistory G ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Cont Sigma preorder G ∧ Cont T I Sigma ∧ Cont G H C ∧ Cont C P N ∧
        PkgSig bundle N pkg

theorem SobrificationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {T I Sigma preorder G H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobrificationCarrier T I Sigma preorder G H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun _row : BHist => Cont Sigma preorder G ∧ Cont T I Sigma)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont G H C ∧ Cont C P N)
        (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  obtain ⟨_unaryT, _unaryI, _unarySigma, _unaryPreorder, _unaryG, _unaryH,
    _unaryC, _unaryP, unaryN, routeSigmaPreorderG, routeTISigma, routeGHC,
    routeCPN, pkgN⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro N ⟨hsame_refl N, unaryN, pkgN⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _row' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row _source
      exact ⟨routeSigmaPreorderG, routeTISigma⟩
    ledger_sound := by
      intro row source
      exact ⟨source.right.right, routeGHC, routeCPN⟩
  }

end BEDC.Derived.SobrificationUp
