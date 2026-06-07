import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousNameCertBasisObligations [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead transportRead replayRead
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W -> UnaryHistory R -> UnaryHistory E -> UnaryHistory O ->
        UnaryHistory H -> UnaryHistory C -> UnaryHistory N ->
          Cont W R windowRead -> Cont windowRead E epigraphRead ->
            Cont epigraphRead O locatedRead -> Cont locatedRead H transportRead ->
              Cont transportRead C replayRead -> Cont replayRead N realSeal ->
                PkgSig bundle P pkg -> PkgSig bundle N pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row epigraphRead ∨ hsame row locatedRead ∨
                          hsame row replayRead ∨ hsame row realSeal) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row E ∨ hsame row W ∨ hsame row R ∨ hsame row O ∨
                          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                            Cont W R windowRead ∨ Cont windowRead E epigraphRead ∨
                              Cont epigraphRead O locatedRead ∨
                                Cont locatedRead H transportRead ∨
                                  Cont transportRead C replayRead ∨
                                    Cont replayRead N realSeal)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont W R windowRead ∧
                          Cont windowRead E epigraphRead ∧
                            Cont epigraphRead O locatedRead ∧
                              Cont locatedRead H transportRead ∧
                                Cont transportRead C replayRead ∧
                                  Cont replayRead N realSeal ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle N pkg)
                      hsame ∧ UnaryHistory epigraphRead ∧ UnaryHistory locatedRead ∧
                    UnaryHistory replayRead ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro fields wUnary rUnary eUnary oUnary hUnary cUnary nUnary windowRoute epigraphRoute
    locatedRoute transportRoute replayRoute sealRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed replayUnary nUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row epigraphRead ∨ hsame row locatedRead ∨ hsame row replayRead ∨
              hsame row realSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row W ∨ hsame row R ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ Cont W R windowRead ∨
                Cont windowRead E epigraphRead ∨ Cont epigraphRead O locatedRead ∨
                  Cont locatedRead H transportRead ∨ Cont transportRead C replayRead ∨
                    Cont replayRead N realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ Cont locatedRead H transportRead ∧
                Cont transportRead C replayRead ∧ Cont replayRead N realSeal ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro epigraphRead
        ⟨Or.inl (hsame_refl epigraphRead), epigraphUnary⟩
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
          | inl sameEpigraph =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameEpigraph)
          | inr rest =>
              cases rest with
              | inl sameLocated =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameLocated))
              | inr rest =>
                  cases rest with
                  | inl sameReplay =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameReplay)))
                  | inr sameSeal =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) sameSeal)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameEpigraph =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl epigraphRoute)))))))))
      | inr rest =>
          cases rest with
          | inl _sameLocated =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr (Or.inl locatedRoute))))))))))
          | inr rest =>
              cases rest with
              | inl _sameReplay =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl replayRoute))))))))))))
              | inr _sameSeal =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sealRoute))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, epigraphRoute, locatedRoute, transportRoute, replayRoute,
          sealRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, epigraphUnary, locatedUnary, replayUnary, realSealUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
