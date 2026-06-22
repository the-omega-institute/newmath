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

theorem SetlikeTypeLikeFirstOrderModelTheoryConsumerBoundary [AskSetup] [PackageSetup]
    (S : SetlikeUp)
    {M Q I R E H C P N membershipRead subsetRead comprehensionRead extensionalRead
      boundaryRead firstOrderRead modelRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory N ->
                      Cont M Q membershipRead ->
                        Cont Q I subsetRead ->
                          Cont R E comprehensionRead ->
                            Cont membershipRead subsetRead extensionalRead ->
                              Cont extensionalRead H boundaryRead ->
                                Cont boundaryRead C firstOrderRead ->
                                  Cont firstOrderRead C modelRead ->
                                    Cont modelRead N namedRead ->
                                      PkgSig bundle P pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row namedRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row M ∨ hsame row Q ∨
                                                hsame row I ∨ hsame row R ∨
                                                  hsame row E ∨ hsame row boundaryRead ∨
                                                    hsame row firstOrderRead ∨
                                                      hsame row modelRead ∨
                                                        hsame row namedRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont M Q membershipRead ∧
                                                  Cont Q I subsetRead ∧
                                                    Cont R E comprehensionRead ∧
                                                      Cont membershipRead subsetRead
                                                        extensionalRead ∧
                                                        Cont extensionalRead H boundaryRead ∧
                                                          Cont boundaryRead C
                                                            firstOrderRead ∧
                                                            Cont firstOrderRead C
                                                              modelRead ∧
                                                              Cont modelRead N namedRead ∧
                                                                PkgSig bundle P pkg)
                                            hsame ∧
                                          UnaryHistory boundaryRead ∧
                                            UnaryHistory firstOrderRead ∧
                                              UnaryHistory modelRead ∧
                                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE rowsH rowsC rowsN membershipRoute
    subsetRoute comprehensionRoute extensionalRoute boundaryRoute firstOrderRoute
    modelRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have _comprehensionUnary : UnaryHistory comprehensionRead :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have extensionalUnary : UnaryHistory extensionalRead :=
    unary_cont_closed membershipUnary subsetUnary extensionalRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed extensionalUnary rowsH boundaryRoute
  have firstOrderUnary : UnaryHistory firstOrderRead :=
    unary_cont_closed boundaryUnary rowsC firstOrderRoute
  have modelUnary : UnaryHistory modelRead :=
    unary_cont_closed firstOrderUnary rowsC modelRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed modelUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row boundaryRead ∨ hsame row firstOrderRead ∨ hsame row modelRead ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipRead ∧ Cont Q I subsetRead ∧
              Cont R E comprehensionRead ∧ Cont membershipRead subsetRead extensionalRead ∧
                Cont extensionalRead H boundaryRead ∧ Cont boundaryRead C firstOrderRead ∧
                  Cont firstOrderRead C modelRead ∧ Cont modelRead N namedRead ∧
                    PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, membershipRoute, subsetRoute, comprehensionRoute, extensionalRoute,
          boundaryRoute, firstOrderRoute, modelRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, boundaryUnary, firstOrderUnary, modelUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
