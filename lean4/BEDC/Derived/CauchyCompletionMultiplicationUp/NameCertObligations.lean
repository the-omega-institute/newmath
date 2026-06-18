import BEDC.Derived.CauchyCompletionMultiplicationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionMultiplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionMultiplicationCarrier [AskSetup] [PackageSetup]
    (M O I A S R D E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory M ∧ UnaryHistory O ∧ UnaryHistory I ∧ UnaryHistory A ∧
    UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        hsame H M ∧ hsame C P ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchyCompletionMultiplicationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M O I A S R D E H C P N flattenRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMultiplicationCarrier M O I A S R D E H C P N bundle pkg ->
      Cont M O flattenRead ->
        Cont S R sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row O ∨ hsame row I ∨ hsame row A ∨
                    hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
                      hsame row sealRead)
                (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory flattenRead ∧ UnaryHistory sealRead ∧ Cont M O flattenRead ∧
                Cont S R sealRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig
  intro carrier flattenRoute sealRoute sealPkg
  obtain ⟨mUnary, oUnary, _iUnary, _aUnary, sUnary, rUnary, _dUnary, _eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _hM, _cP, provenancePkg, _namePkg⟩ := carrier
  have flattenUnary : UnaryHistory flattenRead :=
    unary_cont_closed mUnary oUnary flattenRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sUnary rUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row O ∨ hsame row I ∨ hsame row A ∨
              hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
                hsame row sealRead)
          (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sealPkg⟩
  }
  exact
    ⟨cert, flattenUnary, sealUnary, flattenRoute, sealRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.CauchyCompletionMultiplicationUp
