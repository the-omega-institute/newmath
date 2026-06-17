import BEDC.Derived.BolzanoWeierstrassSelectorUp.RootWindow

namespace BEDC.Derived.BolzanoWeierstrassSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassSelectorPublicExport [AskSetup] [PackageSetup]
    {B M Q W D R E _H _C P _N selectedWindow dyadicRead regularRead realSeal
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B M selectedWindow ->
      Cont selectedWindow Q W ->
        Cont W D dyadicRead ->
          Cont dyadicRead R regularRead ->
            Cont regularRead E realSeal ->
              Cont realSeal P publicRead ->
                UnaryHistory B ->
                  UnaryHistory M ->
                    UnaryHistory Q ->
                      UnaryHistory D ->
                        UnaryHistory R ->
                          UnaryHistory E ->
                            UnaryHistory P ->
                              PkgSig bundle publicRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row B ∨ hsame row M ∨ hsame row Q ∨
                                        hsame row W ∨ hsame row D ∨ hsame row R ∨
                                          hsame row E ∨ hsame row publicRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                                    hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro selectedRoute windowRoute dyadicRoute regularRoute sealRoute publicRoute unaryB unaryM
    unaryQ unaryD unaryR unaryE unaryP publicPkg
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed unaryB unaryM selectedRoute
  have windowUnary : UnaryHistory W :=
    unary_cont_closed selectedUnary unaryQ windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary unaryD dyadicRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicUnary unaryR regularRoute
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed regularUnary unaryE sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary unaryP publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row M ∨ hsame row Q ∨ hsame row W ∨ hsame row D ∨
              hsame row R ∨ hsame row E ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact ⟨source.right, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.BolzanoWeierstrassSelectorUp
