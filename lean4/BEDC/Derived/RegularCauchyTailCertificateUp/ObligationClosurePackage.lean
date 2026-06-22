import BEDC.Derived.RegularCauchyTailCertificateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTailCertificateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailCertificateObligationClosurePackage [AskSetup] [PackageSetup]
    {X W R D E H C P N sourceWindow readbackRoute dyadicRoute realRoute support
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    regularCauchyTailCertificateFields (RegularCauchyTailCertificateUp.mk X W R D E H C P N) =
        [X, W, R, D, E, H, C, P, N] →
      UnaryHistory X →
        UnaryHistory W →
          UnaryHistory R →
            UnaryHistory D →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory N →
                      Cont X W sourceWindow →
                        Cont sourceWindow R readbackRoute →
                          Cont readbackRoute D dyadicRoute →
                            Cont dyadicRoute E realRoute →
                              Cont H C support →
                                Cont support N namedRead →
                                  PkgSig bundle namedRead pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row X ∨ hsame row W ∨ hsame row R ∨
                                            hsame row D ∨ hsame row E ∨ hsame row H ∨
                                              hsame row C ∨ hsame row N ∨
                                                hsame row namedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont X W sourceWindow ∧
                                            Cont sourceWindow R readbackRoute ∧
                                              Cont readbackRoute D dyadicRoute ∧
                                                Cont dyadicRoute E realRoute ∧
                                                  Cont H C support ∧
                                                    Cont support N namedRead ∧
                                                      PkgSig bundle namedRead pkg)
                                        hsame ∧
                                      UnaryHistory sourceWindow ∧ UnaryHistory readbackRoute ∧
                                        UnaryHistory dyadicRoute ∧ UnaryHistory realRoute ∧
                                          UnaryHistory support ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: RegularCauchyTailCertificateUp regularCauchyTailCertificateFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields sourceUnary windowUnary readbackUnary dyadicUnary realUnary transportUnary
    continuationUnary nameUnary sourceWindowRoute readbackRouteStep dyadicRouteStep
    realRouteStep supportRoute namedRoute packageRead
  have _acceptedFields :
      regularCauchyTailCertificateFields
          (RegularCauchyTailCertificateUp.mk X W R D E H C P N) =
        [X, W, R, D, E, H, C, P, N] := fields
  have sourceWindowUnary : UnaryHistory sourceWindow :=
    unary_cont_closed sourceUnary windowUnary sourceWindowRoute
  have readbackRouteUnary : UnaryHistory readbackRoute :=
    unary_cont_closed sourceWindowUnary readbackUnary readbackRouteStep
  have dyadicRouteUnary : UnaryHistory dyadicRoute :=
    unary_cont_closed readbackRouteUnary dyadicUnary dyadicRouteStep
  have realRouteUnary : UnaryHistory realRoute :=
    unary_cont_closed dyadicRouteUnary realUnary realRouteStep
  have supportUnary : UnaryHistory support :=
    unary_cont_closed transportUnary continuationUnary supportRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed supportUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W sourceWindow ∧
              Cont sourceWindow R readbackRoute ∧ Cont readbackRoute D dyadicRoute ∧
                Cont dyadicRoute E realRoute ∧ Cont H C support ∧
                  Cont support N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
        ⟨source.right, sourceWindowRoute, readbackRouteStep, dyadicRouteStep, realRouteStep,
          supportRoute, namedRoute, packageRead⟩
  }
  exact
    ⟨cert, sourceWindowUnary, readbackRouteUnary, dyadicRouteUnary, realRouteUnary,
      supportUnary, namedReadUnary⟩

end BEDC.Derived.RegularCauchyTailCertificateUp
