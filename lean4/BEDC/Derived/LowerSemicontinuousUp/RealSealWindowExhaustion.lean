import BEDC.Derived.LowerSemicontinuousUp.LocatedEpigraphTransportInduction

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRealSealWindowExhaustion [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W -> UnaryHistory R -> UnaryHistory E -> UnaryHistory O -> UnaryHistory N ->
        Cont W R windowRead -> Cont windowRead E epigraphRead ->
          Cont epigraphRead O locatedRead -> Cont locatedRead N realSeal ->
            PkgSig bundle P pkg -> PkgSig bundle N pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row R ∨
                      hsame row E ∨ hsame row O ∨ Cont locatedRead N realSeal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W R windowRead ∧
                      Cont windowRead E epigraphRead ∧ Cont epigraphRead O locatedRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory epigraphRead ∧
                  UnaryHistory locatedRead ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields wUnary rUnary eUnary oUnary nUnary windowRoute epigraphRoute locatedRoute
    realSealRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed locatedUnary nUnary realSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row O ∨ Cont locatedRead N realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal
        ⟨hsame_refl realSeal, realSealUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr realSealRoute)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, epigraphRoute, locatedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, windowUnary, epigraphUnary, locatedUnary, realSealUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
