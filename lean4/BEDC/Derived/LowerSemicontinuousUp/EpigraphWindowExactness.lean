import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousEpigraphWindowExactness [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead exactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] →
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] →
        UnaryHistory W →
          UnaryHistory R →
            UnaryHistory E →
              UnaryHistory O →
                Cont W R windowRead →
                  Cont windowRead E epigraphRead →
                    Cont epigraphRead O exactRead →
                      PkgSig bundle P pkg →
                        PkgSig bundle N pkg →
                          SemanticNameCert
                              (fun row : BHist =>
                                (hsame row windowRead ∨ hsame row epigraphRead ∨
                                  hsame row exactRead) ∧
                                  UnaryHistory row)
                              (fun row : BHist =>
                                hsame row W ∨ hsame row R ∨ hsame row E ∨
                                  hsame row O ∨ Cont W R windowRead ∨
                                    Cont windowRead E epigraphRead ∨
                                      Cont epigraphRead O exactRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont W R windowRead ∧
                                  Cont windowRead E epigraphRead ∧
                                    Cont epigraphRead O exactRead ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory windowRead ∧ UnaryHistory epigraphRead ∧
                              UnaryHistory exactRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro rootFields epigraphFields wUnary rUnary eUnary oUnary windowRoute epigraphRoute
    exactRoute provenancePkg namePkg
  have _acceptedRootFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := rootFields
  have _acceptedEpigraphFields :
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := epigraphFields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary eUnary epigraphRoute
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed epigraphUnary oUnary exactRoute
  have sourceWindow :
      (fun row : BHist =>
        (hsame row windowRead ∨ hsame row epigraphRead ∨ hsame row exactRead) ∧
          UnaryHistory row) windowRead := by
    exact ⟨Or.inl (hsame_refl windowRead), windowUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row windowRead ∨ hsame row epigraphRead ∨ hsame row exactRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
              Cont W R windowRead ∨ Cont windowRead E epigraphRead ∨
                Cont epigraphRead O exactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              Cont epigraphRead O exactRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro windowRead sourceWindow
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
          | inl sameWindow =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameWindow)
          | inr rest =>
              cases rest with
              | inl sameEpigraph =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameEpigraph))
              | inr sameExact =>
                  exact
                    Or.inr
                      (Or.inr (hsame_trans (hsame_symm sameRows) sameExact))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl _sameWindow =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl windowRoute))))
      | inr rest =>
          cases rest with
          | inl _sameEpigraph =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl epigraphRoute)))))
          | inr _sameExact =>
              exact
                Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr exactRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, epigraphRoute, exactRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, windowUnary, epigraphUnary, exactUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
