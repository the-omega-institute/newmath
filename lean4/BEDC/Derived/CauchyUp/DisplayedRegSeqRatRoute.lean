import BEDC.Derived.CauchyUp

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDisplayedRegseqratRoute [AskSetup] [PackageSetup]
    {S U D K E H C P N regRead realSeal extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionLeftExactnessCarrier S U D K E H C P N ->
      Cont K E regRead ->
        Cont regRead N realSeal ->
          Cont realSeal H extensionRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle extensionRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row K ∨
                        hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row regRead ∨ hsame row realSeal ∨
                            hsame row extensionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle extensionRead pkg)
                    hsame ∧
                  UnaryHistory regRead ∧ UnaryHistory realSeal ∧
                    UnaryHistory extensionRead ∧ Cont K E regRead ∧
                      Cont regRead N realSeal ∧ Cont realSeal H extensionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier regRoute realSealRoute extensionRoute provenancePkg extensionPkg
  obtain ⟨_sUnary, _uUnary, _dUnary, kUnary, eUnary, hUnary, _cUnary, _pUnary,
    nUnary⟩ := carrier
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed kUnary eUnary regRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regUnary nUnary realSealRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed realSealUnary hUnary extensionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row K ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row regRead ∨ hsame row realSeal ∨
                  hsame row extensionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle extensionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro extensionRead
        ⟨hsame_refl extensionRead, extensionUnary⟩
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
      exact ⟨source.right, provenancePkg, extensionPkg⟩
  }
  exact
    ⟨cert, regUnary, realSealUnary, extensionUnary, regRoute, realSealRoute,
      extensionRoute⟩

end BEDC.Derived.CauchyUp
