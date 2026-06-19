import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionMonadLawUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionMonadLawCarrier [AskSetup] [PackageSetup]
    (M U I B S D R H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory M ∧ UnaryHistory U ∧ UnaryHistory I ∧ UnaryHistory B ∧
    UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ hsame H C ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchyCompletionMonadLawCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M U I B S D R H C P N unitRead bindRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMonadLawCarrier M U I B S D R H C P N bundle pkg ->
      Cont M U unitRead ->
        Cont I B bindRead ->
          Cont S D regularRead ->
            PkgSig bundle regularRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row U ∨ hsame row I ∨ hsame row B ∨
                      hsame row S ∨ hsame row D ∨ hsame row R ∨ hsame row regularRead)
                  (fun row : BHist =>
                    hsame row regularRead ∧ PkgSig bundle regularRead pkg)
                  hsame ∧
                UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                  UnaryHistory regularRead ∧ Cont M U unitRead ∧ Cont I B bindRead ∧
                    Cont S D regularRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle regularRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig
  intro carrier unitRoute bindRoute regularRoute regularPkg
  obtain ⟨mUnary, uUnary, iUnary, bUnary, sUnary, dUnary, _rUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _hC, provenancePkg, _namePkg⟩ := carrier
  have unitUnary : UnaryHistory unitRead :=
    unary_cont_closed mUnary uUnary unitRoute
  have bindUnary : UnaryHistory bindRead :=
    unary_cont_closed iUnary bUnary bindRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed sUnary dUnary regularRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row U ∨ hsame row I ∨ hsame row B ∨
              hsame row S ∨ hsame row D ∨ hsame row R ∨ hsame row regularRead)
          (fun row : BHist => hsame row regularRead ∧ PkgSig bundle regularRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regularRead
        ⟨hsame_refl regularRead, regularUnary⟩
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
                  (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, regularPkg⟩
  }
  exact
    ⟨cert, unitUnary, bindUnary, regularUnary, unitRoute, bindRoute, regularRoute,
      provenancePkg, regularPkg⟩

end BEDC.Derived.CauchyCompletionMonadLawUp
