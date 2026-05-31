import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DyadicTailBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicTailBallRealEqualityConsumer [AskSetup] [PackageSetup]
    {B D F R H C P N sharedWindow equalityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory F ->
        UnaryHistory R ->
          UnaryHistory N ->
            Cont D F B ->
              Cont B R sharedWindow ->
                Cont sharedWindow N equalityRead ->
                  PkgSig bundle equalityRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row equalityRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row B ∨ hsame row D ∨ hsame row F ∨ hsame row R ∨
                            hsame row sharedWindow ∨ hsame row equalityRead)
                        (fun row : BHist =>
                          hsame row equalityRead ∧ PkgSig bundle equalityRead pkg)
                        hsame ∧
                      UnaryHistory B ∧ UnaryHistory sharedWindow ∧
                        UnaryHistory equalityRead ∧ Cont B R sharedWindow ∧
                          Cont sharedWindow N equalityRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro dyadicUnary filterUnary realUnary nameUnary ballRoute sharedWindowRoute
    equalityRoute equalityPkg
  have ballUnary : UnaryHistory B :=
    unary_cont_closed dyadicUnary filterUnary ballRoute
  have sharedWindowUnary : UnaryHistory sharedWindow :=
    unary_cont_closed ballUnary realUnary sharedWindowRoute
  have equalityUnary : UnaryHistory equalityRead :=
    unary_cont_closed sharedWindowUnary nameUnary equalityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row equalityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row D ∨ hsame row F ∨ hsame row R ∨
              hsame row sharedWindow ∨ hsame row equalityRead)
          (fun row : BHist => hsame row equalityRead ∧ PkgSig bundle equalityRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro equalityRead
        ⟨hsame_refl equalityRead, equalityUnary⟩
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
                (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, equalityPkg⟩
  }
  exact
    ⟨cert, ballUnary, sharedWindowUnary, equalityUnary, sharedWindowRoute, equalityRoute⟩

end BEDC.Derived.DyadicTailBallUp
