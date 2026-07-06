import BEDC.Derived.HallMarriageUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HallMarriageUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HallMarriageCarrier [AskSetup] [PackageSetup]
    (L R E N S B A M U P C T Q : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: HallMarriageUp BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory N ∧
    UnaryHistory S ∧ UnaryHistory B ∧ UnaryHistory A ∧ UnaryHistory M ∧
      UnaryHistory U ∧ UnaryHistory P ∧ UnaryHistory C ∧ UnaryHistory T ∧
        UnaryHistory Q ∧ PkgSig bundle P pkg ∧ PkgSig bundle Q pkg

theorem HallMarriageCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {L R E N S B A M U P C T Q routeName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HallMarriageCarrier L R E N S B A M U P C T Q bundle pkg ->
      Cont A M routeName ->
        PkgSig bundle routeName pkg ->
          SemanticNameCert
              (fun row : BHist =>
                HallMarriageCarrier L R E N S B A M U P C T Q bundle pkg ∧
                  hsame row routeName)
              (fun row : BHist =>
                hsame row L ∨ hsame row R ∨ hsame row E ∨ hsame row N ∨
                  hsame row S ∨ hsame row B ∨ hsame row A ∨ hsame row M ∨
                    hsame row U ∨ hsame row routeName)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont A M routeName ∧ PkgSig bundle routeName pkg)
              hsame := by
  -- BEDC touchpoint anchor: HallMarriageCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier route routePkg
  have carrierFull : HallMarriageCarrier L R E N S B A M U P C T Q bundle pkg := carrier
  obtain ⟨_lUnary, _rUnary, _eUnary, _nUnary, _sUnary, _bUnary, aUnary, mUnary,
    _uUnary, _pUnary, _cUnary, _tUnary, _qUnary, _provenancePkg, _namePkg⟩ := carrier
  have routeUnary : UnaryHistory routeName :=
    unary_cont_closed aUnary mUnary route
  exact {
    core := {
      carrier_inhabited := Exists.intro routeName ⟨carrierFull, hsame_refl routeName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.right))))))))
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport_symm routeUnary source.right, route, routePkg⟩
  }

end BEDC.Derived.HallMarriageUp
