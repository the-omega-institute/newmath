import BEDC.Derived.DyadicUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicUp_obligation_closure_route [AskSetup] [PackageSetup]
    {Q S R E H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCarrier Q S R E H C P N bundle pkg ->
      Cont R E sealRead ->
        PkgSig bundle sealRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row sealRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont Q S R ∧ Cont R E C ∧ Cont R E sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ PkgSig bundle sealRead pkg)
            hsame ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sealRoute sealPkg
  obtain ⟨qUnary, sUnary, rUnary, eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    qsrRoute, recRoute, provenancePkg, namePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary eUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
            hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont Q S R ∧ Cont R E C ∧ Cont R E sealRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ PkgSig bundle sealRead pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, qsrRoute, recRoute, sealRoute, provenancePkg, namePkg, sealPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.DyadicUp
