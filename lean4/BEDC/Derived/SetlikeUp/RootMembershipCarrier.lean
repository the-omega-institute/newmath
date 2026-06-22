import BEDC.Derived.SetlikeUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SetlikeRootMembershipCarrier [AskSetup] [PackageSetup] (S : SetlikeUp)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: SetlikeUp BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  ∃ M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay extensionalReplay
    routeRead namedRead : BHist,
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ∧
      Cont M Q membershipReplay ∧
        Cont Q I subsetReplay ∧
          Cont R E comprehensionReplay ∧
            Cont membershipReplay subsetReplay extensionalReplay ∧
              Cont extensionalReplay comprehensionReplay routeRead ∧
                Cont routeRead N namedRead ∧
                  PkgSig bundle P pkg ∧
                    Nonempty
                      (SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨
                            hsame row E ∨ hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont routeRead N namedRead ∧
                            PkgSig bundle P pkg)
                        hsame)

theorem SetlikeRootMembershipCarrier_route_readback [AskSetup] [PackageSetup]
    (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay extensionalReplay
      routeRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] →
      UnaryHistory M →
        UnaryHistory Q →
          UnaryHistory I →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory N →
                  Cont M Q membershipReplay →
                    Cont Q I subsetReplay →
                      Cont R E comprehensionReplay →
                        Cont membershipReplay subsetReplay extensionalReplay →
                          Cont extensionalReplay comprehensionReplay routeRead →
                            Cont routeRead N namedRead →
                              PkgSig bundle P pkg →
                                SetlikeRootMembershipCarrier S bundle pkg ∧
                                  UnaryHistory routeRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE rowsN membershipRoute subsetRoute
    comprehensionRoute extensionalRoute routeCont namedRoute packageRead
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionReplay :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have extensionalUnary : UnaryHistory extensionalReplay :=
    unary_cont_closed membershipUnary subsetUnary extensionalRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed extensionalUnary comprehensionUnary routeCont
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed routeUnary rowsN namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
            hsame row namedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont routeRead N namedRead ∧ PkgSig bundle P pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namedRoute, packageRead⟩
  }
  exact
    ⟨⟨M, Q, I, R, E, H, C, P, N, membershipReplay, subsetReplay, comprehensionReplay,
      extensionalReplay, routeRead, namedRead, fields, membershipRoute, subsetRoute,
      comprehensionRoute, extensionalRoute, routeCont, namedRoute, packageRead, ⟨cert⟩⟩,
      routeUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
