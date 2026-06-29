import BEDC.Derived.CofinalStreamTailSelectorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalStreamTailSelectorRealSealNonescape [AskSetup] [PackageSetup]
    {eps W R D A sigma H C P N regularRead dyadicRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalStreamTailSelectorCarrier eps W R D A sigma H C P N bundle pkg →
      Cont W R regularRead →
        Cont regularRead D dyadicRead →
          Cont dyadicRead A sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row eps ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                      hsame row A ∨ hsame row sigma ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row regularRead ∨
                          hsame row dyadicRead ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W R regularRead ∧
                      Cont regularRead D dyadicRead ∧ Cont dyadicRead A sealRead ∧
                        PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory regularRead ∧ UnaryHistory dyadicRead ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier regularRoute dyadicRoute sealRoute sealPkg
  obtain ⟨_epsUnary, wUnary, rUnary, dUnary, aUnary, _sigmaUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierPkg⟩ := carrier
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed wUnary rUnary regularRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regularUnary dUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary aUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row eps ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row A ∨ hsame row sigma ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row regularRead ∨
                  hsame row dyadicRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R regularRead ∧
              Cont regularRead D dyadicRead ∧ Cont dyadicRead A sealRead ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regularRoute, dyadicRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, regularUnary, dyadicUnary, sealUnary⟩

end BEDC.Derived.CofinalStreamTailSelectorUp
