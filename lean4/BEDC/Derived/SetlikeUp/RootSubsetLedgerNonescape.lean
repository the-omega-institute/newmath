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

theorem SetlikeRootSubsetLedgerNonescape [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N subsetReplay comprehensionReplay ledgerRead transportRead
      provenanceRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory Q ->
        UnaryHistory I ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont Q I subsetReplay ->
                        Cont R E comprehensionReplay ->
                          Cont subsetReplay comprehensionReplay ledgerRead ->
                            Cont ledgerRead H transportRead ->
                              Cont transportRead P provenanceRead ->
                                Cont provenanceRead N namedRead ->
                                  PkgSig bundle P pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row Q ∨ hsame row I ∨ hsame row R ∨
                                            hsame row E ∨ hsame row H ∨ hsame row P ∨
                                              hsame row N ∨ hsame row namedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont Q I subsetReplay ∧
                                            Cont R E comprehensionReplay ∧
                                              Cont subsetReplay comprehensionReplay ledgerRead ∧
                                                Cont ledgerRead H transportRead ∧
                                                  Cont transportRead P provenanceRead ∧
                                                    Cont provenanceRead N namedRead ∧
                                                      PkgSig bundle P pkg)
                                        hsame ∧
                                      UnaryHistory ledgerRead ∧ UnaryHistory transportRead ∧
                                        UnaryHistory provenanceRead ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsQ rowsI rowsR rowsE rowsH _rowsC rowsP rowsN subsetRoute
    comprehensionRoute ledgerRoute transportRoute provenanceRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionReplay :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed subsetUnary comprehensionUnary ledgerRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed ledgerUnary rowsH transportRoute
  have provenanceUnary : UnaryHistory provenanceRead :=
    unary_cont_closed transportUnary rowsP provenanceRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed provenanceUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row P ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q I subsetReplay ∧ Cont R E comprehensionReplay ∧
              Cont subsetReplay comprehensionReplay ledgerRead ∧
                Cont ledgerRead H transportRead ∧ Cont transportRead P provenanceRead ∧
                  Cont provenanceRead N namedRead ∧ PkgSig bundle P pkg)
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
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, subsetRoute, comprehensionRoute, ledgerRoute, transportRoute,
          provenanceRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, ledgerUnary, transportUnary, provenanceUnary, namedUnary⟩

theorem SetlikeNameCertLedgerNonescape [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay extensionalReplay
      transportReplay namedReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory N ->
                    Cont M Q membershipReplay ->
                      Cont Q I subsetReplay ->
                        Cont R E comprehensionReplay ->
                          Cont membershipReplay subsetReplay extensionalReplay ->
                            Cont extensionalReplay H transportReplay ->
                              Cont transportReplay N namedReplay ->
                                PkgSig bundle P pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedReplay ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                          hsame row R ∨ hsame row E ∨ hsame row H ∨
                                            hsame row N ∨ hsame row namedReplay)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont M Q membershipReplay ∧
                                          Cont Q I subsetReplay ∧
                                            Cont R E comprehensionReplay ∧
                                              Cont membershipReplay subsetReplay
                                                extensionalReplay ∧
                                                Cont extensionalReplay H
                                                  transportReplay ∧
                                                  Cont transportReplay N namedReplay ∧
                                                    PkgSig bundle P pkg)
                                      hsame ∧
                                    UnaryHistory namedReplay := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE rowsH rowsN membershipRoute subsetRoute
    comprehensionRoute extensionalRoute transportRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have _comprehensionUnary : UnaryHistory comprehensionReplay :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have extensionalUnary : UnaryHistory extensionalReplay :=
    unary_cont_closed membershipUnary subsetUnary extensionalRoute
  have transportUnary : UnaryHistory transportReplay :=
    unary_cont_closed extensionalUnary rowsH transportRoute
  have namedUnary : UnaryHistory namedReplay :=
    unary_cont_closed transportUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedReplay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row N ∨ hsame row namedReplay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipReplay ∧ Cont Q I subsetReplay ∧
              Cont R E comprehensionReplay ∧
                Cont membershipReplay subsetReplay extensionalReplay ∧
                  Cont extensionalReplay H transportReplay ∧
                    Cont transportReplay N namedReplay ∧ PkgSig bundle P pkg)
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
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, membershipRoute, subsetRoute, comprehensionRoute, extensionalRoute,
          transportRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.SetlikeUp
