import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RieszInterpolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RieszInterpolationCarrier [AskSetup] [PackageSetup]
    (G L P A B W H C S N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory G ∧ UnaryHistory L ∧ UnaryHistory P ∧ UnaryHistory A ∧
    UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory S ∧ UnaryHistory N ∧ PkgSig bundle S pkg ∧ PkgSig bundle N pkg

theorem RieszInterpolationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {G L P A B W H C S N replayRead witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszInterpolationCarrier G L P A B W H C S N bundle pkg ->
      Cont W H witnessRead ->
        Cont witnessRead C replayRead ->
          PkgSig bundle S pkg ->
            PkgSig bundle N pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row G ∨ hsame row L ∨ hsame row P ∨ hsame row A ∨
                      hsame row B ∨ hsame row W ∨ hsame row witnessRead ∨
                        hsame row replayRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row G ∨ hsame row L ∨ hsame row P ∨ hsame row A ∨
                      hsame row B ∨ hsame row W ∨ hsame row H ∨ hsame row C ∨
                        hsame row S ∨ hsame row N ∨ hsame row witnessRead ∨
                          hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W H witnessRead ∧
                      Cont witnessRead C replayRead ∧ PkgSig bundle S pkg ∧
                        PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory witnessRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: RieszInterpolationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier witnessRoute replayRoute provenancePkg namePkg
  obtain ⟨gUnary, lUnary, pUnary, aUnary, bUnary, wUnary, hUnary, cUnary, _sUnary,
    _nUnary, _carrierPkg, _carrierNamePkg⟩ := carrier
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed wUnary hUnary witnessRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed witnessUnary cUnary replayRoute
  have source :
      (fun row : BHist =>
        (hsame row G ∨ hsame row L ∨ hsame row P ∨ hsame row A ∨ hsame row B ∨
          hsame row W ∨ hsame row witnessRead ∨ hsame row replayRead) ∧
          UnaryHistory row) witnessRead := by
    exact
      ⟨Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr (Or.inr (Or.inl (hsame_refl witnessRead))))))),
        witnessUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row G ∨ hsame row L ∨ hsame row P ∨ hsame row A ∨ hsame row B ∨
              hsame row W ∨ hsame row witnessRead ∨ hsame row replayRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row L ∨ hsame row P ∨ hsame row A ∨ hsame row B ∨
              hsame row W ∨ hsame row H ∨ hsame row C ∨ hsame row S ∨ hsame row N ∨
                hsame row witnessRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W H witnessRead ∧ Cont witnessRead C replayRead ∧
              PkgSig bundle S pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro witnessRead source
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
          intro _row _other sameRows sourceRows
          constructor
          · cases sourceRows.left with
            | inl sameG =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameG)
            | inr rest =>
                cases rest with
                | inl sameL =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameL))
                | inr rest =>
                    cases rest with
                    | inl sameP =>
                        exact
                          Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameP)))
                    | inr rest =>
                        cases rest with
                        | inl sameA =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameA))))
                        | inr rest =>
                            cases rest with
                            | inl sameB =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inl (hsame_trans (hsame_symm sameRows) sameB)))))
                            | inr rest =>
                                cases rest with
                                | inl sameW =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inl
                                                  (hsame_trans (hsame_symm sameRows) sameW))))))
                                | inr rest =>
                                    cases rest with
                                    | inl sameWitness =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inl
                                                        (hsame_trans
                                                          (hsame_symm sameRows)
                                                          sameWitness)))))))
                                    | inr sameReplay =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (hsame_trans
                                                          (hsame_symm sameRows)
                                                          sameReplay)))))))
          · exact unary_transport sourceRows.right sameRows
      }
      pattern_sound := by
        intro _row sourceRows
        cases sourceRows.left with
        | inl sameG =>
            exact Or.inl sameG
        | inr rest =>
            cases rest with
            | inl sameL =>
                exact Or.inr (Or.inl sameL)
            | inr rest =>
                cases rest with
                | inl sameP =>
                    exact Or.inr (Or.inr (Or.inl sameP))
                | inr rest =>
                    cases rest with
                    | inl sameA =>
                        exact Or.inr (Or.inr (Or.inr (Or.inl sameA)))
                    | inr rest =>
                        cases rest with
                        | inl sameB =>
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameB))))
                        | inr rest =>
                            cases rest with
                            | inl sameW =>
                                exact
                                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameW)))))
                            | inr rest =>
                                cases rest with
                                | inl sameWitness =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr (Or.inl sameWitness))))))))))
                                | inr sameReplay =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr (Or.inr sameReplay))))))))))
      ledger_sound := by
        intro _row sourceRows
        exact ⟨sourceRows.right, witnessRoute, replayRoute, provenancePkg, namePkg⟩
    }
  exact ⟨cert, witnessUnary, replayUnary⟩

end BEDC.Derived.RieszInterpolationUp
