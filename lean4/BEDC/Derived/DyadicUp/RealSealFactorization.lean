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

theorem DyadicUpRealSealFactorization [AskSetup] [PackageSetup]
    {Q S R E H C P N realRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCarrier Q S R E H C P N bundle pkg ->
      Cont R E realRead ->
        PkgSig bundle realRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
                hsame row realRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont Q S R ∧ Cont R E realRead ∧
                PkgSig bundle realRead pkg)
            hsame ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier realReadRoute realReadPkg
  obtain ⟨qUnary, sUnary, rUnary, eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    qsrRoute, _recRoute, _provenancePkg, _namePkg⟩ := carrier
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed rUnary eUnary realReadRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row realRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont Q S R ∧ Cont R E realRead ∧ PkgSig bundle realRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, qsrRoute, realReadRoute, realReadPkg⟩
  }
  exact ⟨cert, realReadUnary⟩

end BEDC.Derived.DyadicUp
