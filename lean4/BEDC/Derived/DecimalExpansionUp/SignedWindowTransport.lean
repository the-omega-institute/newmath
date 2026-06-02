import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionSignedWindowTransport [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead signedRead placeRead dyadicRead regseqRead
      realSeal : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory E ->
                Cont D W prefixRead ->
                  hsame signedRead prefixRead ->
                    Cont prefixRead V placeRead ->
                      Cont placeRead Q dyadicRead ->
                        Cont dyadicRead R regseqRead ->
                          Cont regseqRead E realSeal ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle signedRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row signedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row D ∨ hsame row W ∨ hsame row prefixRead ∨
                                        hsame row signedRead ∨ hsame row realSeal)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont D W prefixRead ∧
                                        Cont regseqRead E realSeal ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle signedRead pkg)
                                    hsame ∧
                                  UnaryHistory signedRead ∧ UnaryHistory prefixRead ∧
                                    UnaryHistory placeRead ∧ UnaryHistory dyadicRead ∧
                                      UnaryHistory regseqRead ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary prefixRoute signedSamePrefix placeRoute
    dyadicRoute regseqRoute realRoute provenancePkg signedPkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary prefixRoute
  have signedUnary : UnaryHistory signedRead :=
    unary_transport_symm prefixUnary signedSamePrefix
  have placeUnary : UnaryHistory placeRead :=
    unary_cont_closed prefixUnary vUnary placeRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed placeUnary qUnary dyadicRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed dyadicUnary rUnary regseqRoute
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqUnary eUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row signedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row prefixRead ∨
              hsame row signedRead ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W prefixRead ∧ Cont regseqRead E realSeal ∧
              PkgSig bundle P pkg ∧ PkgSig bundle signedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro signedRead ⟨hsame_refl signedRead, signedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, prefixRoute, realRoute, provenancePkg, signedPkg⟩
  }
  exact
    ⟨cert, signedUnary, prefixUnary, placeUnary, dyadicUnary, regseqUnary, realUnary⟩

end BEDC.Derived.DecimalExpansionUp
