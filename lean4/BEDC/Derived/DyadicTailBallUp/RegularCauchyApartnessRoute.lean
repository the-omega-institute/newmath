import BEDC.Derived.DyadicTailBallUp.RegSeqWindowConsistency
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicTailBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicTailBallRegularCauchyApartnessRoute [AskSetup] [PackageSetup]
    {D F B R sharedWindow equalityRead apartnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D →
      UnaryHistory F →
        UnaryHistory R →
          UnaryHistory sharedWindow →
            Cont D F B →
              Cont B R sharedWindow →
                Cont sharedWindow R equalityRead →
                  Cont equalityRead sharedWindow apartnessRead →
                    PkgSig bundle apartnessRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row apartnessRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row B ∨ hsame row D ∨ hsame row F ∨ hsame row R ∨
                              hsame row sharedWindow ∨ hsame row equalityRead ∨
                                hsame row apartnessRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont B R sharedWindow ∧
                              Cont sharedWindow R equalityRead ∧
                                Cont equalityRead sharedWindow apartnessRead ∧
                                  PkgSig bundle apartnessRead pkg)
                          hsame ∧
                        UnaryHistory B ∧ UnaryHistory equalityRead ∧
                          UnaryHistory apartnessRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro dyadicUnary filterUnary realUnary sharedWindowUnary ballRoute sharedWindowRoute
    equalityRoute apartnessRoute apartnessPkg
  have ballUnary : UnaryHistory B :=
    unary_cont_closed dyadicUnary filterUnary ballRoute
  have equalityUnary : UnaryHistory equalityRead :=
    unary_cont_closed sharedWindowUnary realUnary equalityRoute
  have apartnessUnary : UnaryHistory apartnessRead :=
    unary_cont_closed equalityUnary sharedWindowUnary apartnessRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row apartnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row D ∨ hsame row F ∨ hsame row R ∨
              hsame row sharedWindow ∨ hsame row equalityRead ∨ hsame row apartnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B R sharedWindow ∧
              Cont sharedWindow R equalityRead ∧ Cont equalityRead sharedWindow apartnessRead ∧
                PkgSig bundle apartnessRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro apartnessRead
        ⟨hsame_refl apartnessRead, apartnessUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sharedWindowRoute, equalityRoute, apartnessRoute, apartnessPkg⟩
  }
  exact ⟨cert, ballUnary, equalityUnary, apartnessUnary⟩

end BEDC.Derived.DyadicTailBallUp
