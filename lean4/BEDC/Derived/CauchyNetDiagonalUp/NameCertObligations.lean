import BEDC.Derived.CauchyNetDiagonalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyNetDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyNetDiagonalCarrier [AskSetup] [PackageSetup]
    (A M K T S Q R H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory A ∧ UnaryHistory M ∧ UnaryHistory K ∧ UnaryHistory T ∧
    UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory R ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧
        PkgSig bundle N pkg

theorem CauchyNetDiagonalNameCertObligations [AskSetup] [PackageSetup]
    {A M K T S Q R H C P N obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetDiagonalCarrier A M K T S Q R H C P N bundle pkg →
      Cont A M K →
        Cont K T S →
          Cont S Q R →
            Cont R N obligationRead →
              PkgSig bundle obligationRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row M ∨ hsame row K ∨ hsame row T ∨
                        hsame row S ∨ hsame row Q ∨ hsame row R ∨ hsame row H ∨
                          hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row obligationRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont A M K ∧ Cont K T S ∧ Cont S Q R ∧
                        Cont R N obligationRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle N pkg ∧ PkgSig bundle obligationRead pkg)
                    hsame ∧
                  UnaryHistory obligationRead := by
  -- BEDC touchpoint anchor: CauchyNetDiagonalCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sourceRoute scheduleRoute readbackRoute obligationRoute obligationPkg
  obtain ⟨aUnary, mUnary, kUnary, tUnary, _sUnary, _qUnary, rUnary, _hUnary,
    _cUnary, _pUnary, nUnary, provenancePkg, namePkg⟩ := carrier
  have scheduleUnary : UnaryHistory K :=
    unary_cont_closed aUnary mUnary sourceRoute
  have streamUnary : UnaryHistory S :=
    unary_cont_closed kUnary tUnary scheduleRoute
  have sealUnary : UnaryHistory R :=
    unary_cont_closed streamUnary _qUnary readbackRoute
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed rUnary nUnary obligationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row M ∨ hsame row K ∨ hsame row T ∨ hsame row S ∨
              hsame row Q ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A M K ∧ Cont K T S ∧ Cont S Q R ∧
              Cont R N obligationRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                PkgSig bundle obligationRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obligationRead
        ⟨hsame_refl obligationRead, obligationUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, scheduleRoute, readbackRoute, obligationRoute,
          provenancePkg, namePkg, obligationPkg⟩
  }
  exact ⟨cert, obligationUnary⟩

end BEDC.Derived.CauchyNetDiagonalUp
