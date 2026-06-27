import BEDC.Derived.LocatedIntervalMidpointUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedIntervalMidpointUp.NameCertObligations

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedIntervalMidpointCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {I D E0 E1 B S R Q H C P N parentRead midpointRead bisectionRead windowRead
      readbackRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I ->
      UnaryHistory D ->
        UnaryHistory E0 ->
          UnaryHistory B ->
            UnaryHistory S ->
              UnaryHistory R ->
                UnaryHistory Q ->
                  UnaryHistory H ->
                    Cont I D parentRead ->
                      Cont parentRead E0 midpointRead ->
                        Cont midpointRead B bisectionRead ->
                          Cont bisectionRead S windowRead ->
                            Cont windowRead R readbackRead ->
                              Cont readbackRead Q sealRead ->
                                Cont H sealRead namedRead ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle namedRead pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row I ∨ hsame row D ∨
                                              hsame row E0 ∨ hsame row E1 ∨
                                                hsame row B ∨ hsame row S ∨
                                                  hsame row R ∨ hsame row Q ∨
                                                    hsame row H ∨ hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont I D parentRead ∧
                                              Cont parentRead E0 midpointRead ∧
                                                Cont midpointRead B bisectionRead ∧
                                                  Cont bisectionRead S windowRead ∧
                                                    Cont windowRead R readbackRead ∧
                                                      Cont readbackRead Q sealRead ∧
                                                        Cont H sealRead namedRead ∧
                                                          PkgSig bundle namedRead pkg)
                                          hsame ∧
                                        UnaryHistory parentRead ∧
                                          UnaryHistory midpointRead ∧
                                            UnaryHistory bisectionRead ∧
                                              UnaryHistory windowRead ∧
                                                UnaryHistory readbackRead ∧
                                                  UnaryHistory sealRead ∧
                                                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro iUnary dUnary e0Unary bUnary sUnary rUnary qUnary hUnary parentRoute
    midpointRoute bisectionRoute windowRoute readbackRoute sealRoute namedRoute _pPkg namedPkg
  have parentUnary : UnaryHistory parentRead :=
    unary_cont_closed iUnary dUnary parentRoute
  have midpointUnary : UnaryHistory midpointRead :=
    unary_cont_closed parentUnary e0Unary midpointRoute
  have bisectionUnary : UnaryHistory bisectionRead :=
    unary_cont_closed midpointUnary bUnary bisectionRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bisectionUnary sUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary qUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed hUnary sealUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row D ∨ hsame row E0 ∨ hsame row E1 ∨ hsame row B ∨
              hsame row S ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I D parentRead ∧ Cont parentRead E0 midpointRead ∧
              Cont midpointRead B bisectionRead ∧ Cont bisectionRead S windowRead ∧
                Cont windowRead R readbackRead ∧ Cont readbackRead Q sealRead ∧
                  Cont H sealRead namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, parentRoute, midpointRoute, bisectionRoute, windowRoute,
          readbackRoute, sealRoute, namedRoute, namedPkg⟩
  }
  exact
    ⟨cert, parentUnary, midpointUnary, bisectionUnary, windowUnary, readbackUnary,
      sealUnary, namedUnary⟩

end BEDC.Derived.LocatedIntervalMidpointUp.NameCertObligations
