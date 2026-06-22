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

theorem SetlikeRestrictedComprehensionMembershipFactorization [AskSetup] [PackageSetup]
    (S : SetlikeUp)
    {M Q I R E H C P N membershipRead subsetRead comprehensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              Cont M Q membershipRead ->
                Cont membershipRead I subsetRead ->
                  Cont subsetRead R comprehensionRead ->
                    PkgSig bundle P pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row comprehensionRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨
                              hsame row membershipRead ∨ hsame row subsetRead ∨
                                hsame row comprehensionRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont M Q membershipRead ∧
                              Cont membershipRead I subsetRead ∧
                                Cont subsetRead R comprehensionRead ∧ PkgSig bundle P pkg)
                          hsame ∧ UnaryHistory membershipRead ∧ UnaryHistory subsetRead ∧
                        UnaryHistory comprehensionRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR membershipRoute subsetRoute comprehensionRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed membershipUnary rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionRead :=
    unary_cont_closed subsetUnary rowsR comprehensionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comprehensionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨
              hsame row membershipRead ∨ hsame row subsetRead ∨ hsame row comprehensionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipRead ∧
              Cont membershipRead I subsetRead ∧ Cont subsetRead R comprehensionRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro comprehensionRead ⟨hsame_refl comprehensionRead, comprehensionUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, membershipRoute, subsetRoute, comprehensionRoute, packageRead⟩
  }
  exact ⟨cert, membershipUnary, subsetUnary, comprehensionUnary⟩

end BEDC.Derived.SetlikeUp
