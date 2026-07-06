import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AbelTransformationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AbelTransformationCarrier [AskSetup] [PackageSetup]
    (S P C Delta B W T R D E H K Q N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: AbelTransformationUp BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory S ∧ UnaryHistory P ∧ UnaryHistory C ∧ UnaryHistory Delta ∧
    UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory T ∧ UnaryHistory R ∧
      UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory K ∧
        UnaryHistory Q ∧ UnaryHistory N ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg

theorem AbelTransformationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S P C Delta B W T R D E H K Q N transformRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AbelTransformationCarrier S P C Delta B W T R D E H K Q N bundle pkg ->
      Cont S P transformRead ->
        Cont transformRead W sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  AbelTransformationCarrier S P C Delta B W T R D E H K Q N bundle pkg ∧
                    hsame row sealRead)
                (fun row : BHist =>
                  hsame row S ∨ hsame row P ∨ hsame row C ∨ hsame row Delta ∨
                    hsame row B ∨ hsame row W ∨ hsame row T ∨ hsame row R ∨
                      hsame row D ∨ hsame row E ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont S P transformRead ∧
                    Cont transformRead W sealRead ∧ PkgSig bundle sealRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: AbelTransformationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier transformRoute sealRoute sealPkg
  have carrierFull :
      AbelTransformationCarrier S P C Delta B W T R D E H K Q N bundle pkg := carrier
  obtain ⟨sUnary, pUnary, _cUnary, _deltaUnary, _bUnary, wUnary, _tUnary, _rUnary,
    _dUnary, _eUnary, _hUnary, _kUnary, _qUnary, _nUnary, _provenancePkg,
    _namePkg⟩ := carrier
  have transformUnary : UnaryHistory transformRead :=
    unary_cont_closed sUnary pUnary transformRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed transformUnary wUnary sealRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨carrierFull, hsame_refl sealRead⟩
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
                        (Or.inr
                          (Or.inr source.right)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport_symm sealUnary source.right, transformRoute, sealRoute, sealPkg⟩
  }

end BEDC.Derived.AbelTransformationUp
