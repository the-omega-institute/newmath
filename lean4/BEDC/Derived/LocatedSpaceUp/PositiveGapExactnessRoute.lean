import BEDC.Derived.LocatedSpaceUp.NameCertObligations

namespace BEDC.Derived.LocatedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSpaceCarrier_positive_gap_exactness_route [AskSetup] [PackageSetup]
    {X R A G W Q E H C P N requestRead gapRead windowRead readbackRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X →
      UnaryHistory R →
        UnaryHistory A →
          UnaryHistory G →
            UnaryHistory W →
              UnaryHistory Q →
                UnaryHistory E →
                  UnaryHistory N →
                    Cont X R requestRead →
                      Cont A G gapRead →
                        Cont requestRead W windowRead →
                          Cont windowRead Q readbackRead →
                            Cont readbackRead E sealRead →
                              Cont sealRead N namedRead →
                                PkgSig bundle namedRead pkg →
                                  SemanticNameCert
                                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row A ∨ hsame row G ∨ hsame row gapRead ∨
                                          hsame row W ∨ hsame row Q ∨ hsame row E ∨
                                            hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont A G gapRead ∧
                                          Cont readbackRead E sealRead ∧
                                            Cont sealRead N namedRead ∧
                                              PkgSig bundle namedRead pkg)
                                      hsame ∧
                                    UnaryHistory gapRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro xUnary rUnary aUnary gUnary wUnary qUnary eUnary nUnary requestRoute gapRoute
    windowRoute readbackRoute sealRoute namedRoute namedPkg
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed xUnary rUnary requestRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed aUnary gUnary gapRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed requestUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row G ∨ hsame row gapRead ∨ hsame row W ∨
              hsame row Q ∨ hsame row E ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A G gapRead ∧ Cont readbackRead E sealRead ∧
              Cont sealRead N namedRead ∧ PkgSig bundle namedRead pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, gapRoute, sealRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, gapUnary, namedUnary⟩

end BEDC.Derived.LocatedSpaceUp
