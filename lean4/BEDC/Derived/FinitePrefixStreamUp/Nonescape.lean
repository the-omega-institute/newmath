import BEDC.Derived.FinitePrefixStreamUp.NameCertObligations

namespace BEDC.Derived.FinitePrefixStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FinitePrefixStreamCarrier_nonescape [AskSetup] [PackageSetup]
    {k W D R H C P N prefixRead dyadicRead regularRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory k → UnaryHistory W → UnaryHistory D → UnaryHistory R →
      UnaryHistory N → Cont k W prefixRead → Cont prefixRead D dyadicRead →
        Cont dyadicRead R regularRead → Cont regularRead N namedRead →
          PkgSig bundle P pkg → PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                    hsame row namedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont k W prefixRead ∧
                    Cont prefixRead D dyadicRead ∧ Cont dyadicRead R regularRead ∧
                      Cont regularRead N namedRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg)
                hsame ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert
  intro unaryK unaryW unaryD unaryR unaryN prefixRoute dyadicRoute regularRoute
    namedRoute provenancePkg localNamePkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryK unaryW prefixRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed prefixUnary unaryD dyadicRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicUnary unaryR regularRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed regularUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont k W prefixRead ∧
              Cont prefixRead D dyadicRead ∧ Cont dyadicRead R regularRead ∧
                Cont regularRead N namedRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact
        ⟨source.right, prefixRoute, dyadicRoute, regularRoute, namedRoute,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.FinitePrefixStreamUp
