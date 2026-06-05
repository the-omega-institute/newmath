import BEDC.Derived.CauchyUniformNetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyUniformNetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyUniformNetNameCertObligations [BEDC.FKernel.Ask.AskSetup] [PackageSetup]
    {I F U W R E H C P N filterRead toleranceRead windowRead readbackRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I →
      UnaryHistory F →
        UnaryHistory U →
          UnaryHistory W →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont I F filterRead →
                          Cont filterRead U toleranceRead →
                            Cont toleranceRead W windowRead →
                              Cont windowRead R readbackRead →
                                Cont readbackRead E sealRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle sealRead pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            (hsame row I ∨ hsame row F ∨ hsame row U ∨
                                              hsame row W ∨ hsame row R ∨ hsame row E ∨
                                                hsame row sealRead) ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row I ∨ hsame row F ∨ hsame row U ∨
                                              hsame row W ∨ hsame row R ∨ hsame row E ∨
                                                hsame row H ∨ hsame row C ∨ hsame row P ∨
                                                  hsame row N ∨ hsame row sealRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                              PkgSig bundle sealRead pkg ∧ Cont I F filterRead ∧
                                                Cont filterRead U toleranceRead ∧
                                                  Cont toleranceRead W windowRead ∧
                                                    Cont windowRead R readbackRead ∧
                                                      Cont readbackRead E sealRead)
                                          hsame ∧
                                        UnaryHistory filterRead ∧
                                          UnaryHistory toleranceRead ∧
                                            UnaryHistory windowRead ∧
                                              UnaryHistory readbackRead ∧
                                                UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyUniformNetUp BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro indexUnary filterUnary toleranceUnary windowUnary readbackUnary sealUnary
    _transportUnary _continuationUnary provenanceUnary _nameUnary filterRoute toleranceRoute
    windowRoute readbackRoute sealRoute provenancePkg sealPkg
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed indexUnary filterUnary filterRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed filterReadUnary toleranceUnary toleranceRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceReadUnary windowUnary windowRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowReadUnary readbackUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary sealUnary sealRoute
  have sourceSeal :
      (fun row : BHist =>
        (hsame row I ∨ hsame row F ∨ hsame row U ∨ hsame row W ∨ hsame row R ∨
          hsame row E ∨ hsame row sealRead) ∧ UnaryHistory row) sealRead := by
    exact
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (hsame_refl sealRead)))))), sealReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row I ∨ hsame row F ∨ hsame row U ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row sealRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row F ∨ hsame row U ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg ∧
              Cont I F filterRead ∧ Cont filterRead U toleranceRead ∧
                Cont toleranceRead W windowRead ∧ Cont windowRead R readbackRead ∧
                  Cont readbackRead E sealRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
        constructor
        · cases source.left with
          | inl sameIndex =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameIndex)
          | inr rest =>
              cases rest with
              | inl sameFilter =>
                  exact Or.inr (Or.inl
                    (hsame_trans (hsame_symm sameRows) sameFilter))
              | inr rest =>
                  cases rest with
                  | inl sameTolerance =>
                      exact Or.inr (Or.inr (Or.inl
                        (hsame_trans (hsame_symm sameRows) sameTolerance)))
                  | inr rest =>
                      cases rest with
                      | inl sameWindow =>
                          exact Or.inr (Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm sameRows) sameWindow))))
                      | inr rest =>
                          cases rest with
                          | inl sameReadback =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                                (hsame_trans (hsame_symm sameRows) sameReadback)))))
                          | inr rest =>
                              cases rest with
                              | inl sameSealBoundary =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                                    (hsame_trans (hsame_symm sameRows)
                                      sameSealBoundary))))))
                              | inr sameSealRead =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                    (hsame_trans (hsame_symm sameRows) sameSealRead))))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameIndex =>
          exact Or.inl sameIndex
      | inr rest =>
          cases rest with
          | inl sameFilter =>
              exact Or.inr (Or.inl sameFilter)
          | inr rest =>
              cases rest with
              | inl sameTolerance =>
                  exact Or.inr (Or.inr (Or.inl sameTolerance))
              | inr rest =>
                  cases rest with
                  | inl sameWindow =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl sameWindow)))
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameReadback))))
                      | inr rest =>
                          cases rest with
                          | inl sameSealBoundary =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                (Or.inl sameSealBoundary)))))
                          | inr sameSealRead =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                (Or.inr (Or.inr (Or.inr (Or.inr sameSealRead)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, provenancePkg, sealPkg, filterRoute, toleranceRoute, windowRoute,
          readbackRoute, sealRoute⟩
  }
  exact
    ⟨cert, filterReadUnary, toleranceReadUnary, windowReadUnary, readbackReadUnary,
      sealReadUnary⟩

end BEDC.Derived.CauchyUniformNetUp
