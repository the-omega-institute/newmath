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

theorem SetlikeRootMembershipObligation [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay transportedReplay continuedReplay
      provenanceReplay namedReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory H ->
            UnaryHistory C ->
              UnaryHistory P ->
                UnaryHistory N ->
                  Cont M Q membershipReplay ->
                    Cont membershipReplay H transportedReplay ->
                      Cont transportedReplay C continuedReplay ->
                        Cont continuedReplay P provenanceReplay ->
                          Cont provenanceReplay N namedReplay ->
                            PkgSig bundle P pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedReplay ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row M ∨ hsame row Q ∨ hsame row H ∨
                                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                                        hsame row membershipReplay ∨
                                          hsame row transportedReplay ∨
                                            hsame row continuedReplay ∨
                                              hsame row provenanceReplay ∨
                                                hsame row namedReplay)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont M Q membershipReplay ∧
                                      Cont membershipReplay H transportedReplay ∧
                                        Cont transportedReplay C continuedReplay ∧
                                          Cont continuedReplay P provenanceReplay ∧
                                            Cont provenanceReplay N namedReplay ∧
                                              PkgSig bundle P pkg)
                                  hsame ∧
                                UnaryHistory membershipReplay ∧
                                  UnaryHistory transportedReplay ∧
                                    UnaryHistory continuedReplay ∧
                                      UnaryHistory provenanceReplay ∧
                                        UnaryHistory namedReplay := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsH rowsC rowsP rowsN membershipRoute transportedRoute
    continuedRoute provenanceRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have transportedUnary : UnaryHistory transportedReplay :=
    unary_cont_closed membershipUnary rowsH transportedRoute
  have continuedUnary : UnaryHistory continuedReplay :=
    unary_cont_closed transportedUnary rowsC continuedRoute
  have provenanceUnary : UnaryHistory provenanceReplay :=
    unary_cont_closed continuedUnary rowsP provenanceRoute
  have namedUnary : UnaryHistory namedReplay :=
    unary_cont_closed provenanceUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedReplay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row membershipReplay ∨ hsame row transportedReplay ∨
                hsame row continuedReplay ∨ hsame row provenanceReplay ∨
                  hsame row namedReplay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipReplay ∧
              Cont membershipReplay H transportedReplay ∧
                Cont transportedReplay C continuedReplay ∧
                  Cont continuedReplay P provenanceReplay ∧
                    Cont provenanceReplay N namedReplay ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedReplay ⟨hsame_refl namedReplay, namedUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, membershipRoute, transportedRoute, continuedRoute, provenanceRoute,
          namedRoute, packageRead⟩
  }
  exact
    ⟨cert, membershipUnary, transportedUnary, continuedUnary, provenanceUnary, namedUnary⟩

theorem SetlikeTypeLikeFamilyNonescape [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay extensionalReplay
      routeRead namedRead typeFamilyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont M Q membershipReplay ->
                          Cont Q I subsetReplay ->
                            Cont R E comprehensionReplay ->
                              Cont membershipReplay subsetReplay extensionalReplay ->
                                Cont extensionalReplay comprehensionReplay routeRead ->
                                  Cont routeRead N namedRead ->
                                    Cont namedRead P typeFamilyRead ->
                                      PkgSig bundle P pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row typeFamilyRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                                hsame row R ∨ hsame row E ∨
                                                  hsame row namedRead ∨
                                                    hsame row typeFamilyRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont routeRead N namedRead ∧
                                                Cont namedRead P typeFamilyRead ∧
                                                  PkgSig bundle P pkg)
                                            hsame ∧
                                          UnaryHistory typeFamilyRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE _rowsH _rowsC rowsP rowsN membershipRoute
    subsetRoute comprehensionRoute extensionalRoute routeReadRoute namedRoute familyRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionReplay :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have extensionalUnary : UnaryHistory extensionalReplay :=
    unary_cont_closed membershipUnary subsetUnary extensionalRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed extensionalUnary comprehensionUnary routeReadRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed routeUnary rowsN namedRoute
  have typeFamilyUnary : UnaryHistory typeFamilyRead :=
    unary_cont_closed namedUnary rowsP familyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row typeFamilyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row namedRead ∨ hsame row typeFamilyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont routeRead N namedRead ∧
              Cont namedRead P typeFamilyRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro typeFamilyRead ⟨hsame_refl typeFamilyRead, typeFamilyUnary⟩
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
      exact ⟨source.right, namedRoute, familyRoute, packageRead⟩
  }
  exact ⟨cert, typeFamilyUnary⟩

end BEDC.Derived.SetlikeUp
