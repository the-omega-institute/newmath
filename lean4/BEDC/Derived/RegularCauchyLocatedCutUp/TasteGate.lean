import BEDC.Derived.RegularCauchyLocatedCutUp

namespace BEDC.Derived.RegularCauchyLocatedCutUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyLocatedCutRealSealHandoff [AskSetup] [PackageSetup]
    (K : RegularCauchyLocatedCutUp)
    {S Q D L R H C P N windowRead dyadicRead cutRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    regularCauchyLocatedCutFields K = [S, Q, D, L, R, H, C, P, N] ->
      UnaryHistory S ->
        UnaryHistory Q ->
          UnaryHistory D ->
            UnaryHistory L ->
              UnaryHistory R ->
                Cont S Q windowRead ->
                  Cont windowRead D dyadicRead ->
                    Cont dyadicRead L cutRead ->
                      Cont cutRead R realSeal ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle realSeal pkg ->
                            SemanticNameCert
                              (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row S ∨ hsame row Q ∨ hsame row D ∨
                                  hsame row L ∨ hsame row R ∨ hsame row realSeal)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont S Q windowRead ∧
                                  Cont windowRead D dyadicRead ∧ Cont dyadicRead L cutRead ∧
                                    Cont cutRead R realSeal ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle realSeal pkg)
                              hsame ∧
                              UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fieldsEq streamUnary rationalUnary dyadicUnary cutUnary realUnary
    streamRationalWindow windowDyadicRead dyadicCutRead cutRealSeal provenancePkg realSealPkg
  cases K with
  | mk KS KQ KD KL KR KH KC KP KN =>
      unfold regularCauchyLocatedCutFields at fieldsEq
      injection fieldsEq with hS tail0
      injection tail0 with hQ tail1
      injection tail1 with hD tail2
      injection tail2 with hL tail3
      injection tail3 with hR tail4
      injection tail4 with hH tail5
      injection tail5 with hC tail6
      injection tail6 with hP tail7
      injection tail7 with hN _
      subst hS
      subst hQ
      subst hD
      subst hL
      subst hR
      subst hH
      subst hC
      subst hP
      subst hN
      have windowUnary : UnaryHistory windowRead :=
        unary_cont_closed streamUnary rationalUnary streamRationalWindow
      have dyadicReadUnary : UnaryHistory dyadicRead :=
        unary_cont_closed windowUnary dyadicUnary windowDyadicRead
      have cutReadUnary : UnaryHistory cutRead :=
        unary_cont_closed dyadicReadUnary cutUnary dyadicCutRead
      have realSealUnary : UnaryHistory realSeal :=
        unary_cont_closed cutReadUnary realUnary cutRealSeal
      have cert :
          SemanticNameCert
              (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row KS ∨ hsame row KQ ∨ hsame row KD ∨ hsame row KL ∨
                  hsame row KR ∨ hsame row realSeal)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont KS KQ windowRead ∧
                  Cont windowRead KD dyadicRead ∧ Cont dyadicRead KL cutRead ∧
                    Cont cutRead KR realSeal ∧ PkgSig bundle KP pkg ∧
                      PkgSig bundle realSeal pkg)
              hsame := {
        core := {
          carrier_inhabited :=
            Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
          right
          right
          right
          right
          right
          exact source.left
        ledger_sound := by
          intro _row source
          exact
            ⟨source.right, streamRationalWindow, windowDyadicRead, dyadicCutRead,
              cutRealSeal, provenancePkg, realSealPkg⟩
      }
      exact ⟨cert, realSealUnary⟩

end BEDC.Derived.RegularCauchyLocatedCutUp
