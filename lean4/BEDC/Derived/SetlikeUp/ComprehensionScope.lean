import BEDC.Derived.SetlikeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeRootComprehensionScope [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N restrictedRead extensionalRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                Cont M Q restrictedRead ->
                  Cont I R extensionalRead ->
                    Cont restrictedRead extensionalRead scopedRead ->
                      PkgSig bundle P pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                hsame row R ∨ hsame row E ∨ hsame row restrictedRead ∨
                                  hsame row extensionalRead ∨ hsame row scopedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont M Q restrictedRead ∧
                                Cont I R extensionalRead ∧
                                  Cont restrictedRead extensionalRead scopedRead ∧
                                    PkgSig bundle P pkg)
                            hsame ∧
                          UnaryHistory restrictedRead ∧ UnaryHistory extensionalRead ∧
                            UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE membershipRoute extensionalRoute scopedRoute
    packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have restrictedUnary : UnaryHistory restrictedRead :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have extensionalUnary : UnaryHistory extensionalRead :=
    unary_cont_closed rowsI rowsR extensionalRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed restrictedUnary extensionalUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row restrictedRead ∨ hsame row extensionalRead ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q restrictedRead ∧ Cont I R extensionalRead ∧
              Cont restrictedRead extensionalRead scopedRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, membershipRoute, extensionalRoute, scopedRoute, packageRead⟩
  }
  exact ⟨cert, restrictedUnary, extensionalUnary, scopedUnary⟩

end BEDC.Derived.SetlikeUp
