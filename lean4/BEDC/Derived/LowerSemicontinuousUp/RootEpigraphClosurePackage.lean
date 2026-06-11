import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootEpigraphClosurePackage [AskSetup] [PackageSetup]
    {X F E W R O H C P N sourceRead graphRead epigraphRead carrierRead windowRead
      thresholdRead locatedRead realSeal closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory F ->
          UnaryHistory W ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory O ->
                  UnaryHistory N ->
                    Cont X F sourceRead ->
                      Cont sourceRead W graphRead ->
                        Cont graphRead E epigraphRead ->
                          Cont epigraphRead O carrierRead ->
                            Cont W R windowRead ->
                              Cont windowRead E thresholdRead ->
                                Cont thresholdRead O locatedRead ->
                                  Cont locatedRead N realSeal ->
                                    Cont carrierRead realSeal closureRead ->
                                      PkgSig bundle P pkg ->
                                        PkgSig bundle N pkg ->
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row closureRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row X ∨ hsame row F ∨ hsame row W ∨
                                                  hsame row R ∨ hsame row E ∨ hsame row O ∨
                                                    hsame row N ∨ hsame row carrierRead ∨
                                                      hsame row realSeal ∨ hsame row closureRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont X F sourceRead ∧
                                                  Cont sourceRead W graphRead ∧
                                                    Cont graphRead E epigraphRead ∧
                                                      Cont epigraphRead O carrierRead ∧
                                                        Cont W R windowRead ∧
                                                          Cont windowRead E thresholdRead ∧
                                                            Cont thresholdRead O locatedRead ∧
                                                              Cont locatedRead N realSeal ∧
                                                                Cont carrierRead realSeal
                                                                  closureRead ∧
                                                                  PkgSig bundle P pkg ∧
                                                                    PkgSig bundle N pkg)
                                              hsame ∧
                                            UnaryHistory closureRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro fields xUnary fUnary wUnary rUnary eUnary oUnary nUnary sourceRoute graphRoute
    epigraphRoute carrierRoute windowRoute thresholdRoute locatedRoute realSealRoute
    closureRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := fields
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed xUnary fUnary sourceRoute
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed sourceUnary wUnary graphRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed graphUnary eUnary epigraphRoute
  have carrierUnary : UnaryHistory carrierRead :=
    unary_cont_closed epigraphUnary oUnary carrierRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed windowUnary eUnary thresholdRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed thresholdUnary oUnary locatedRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed locatedUnary nUnary realSealRoute
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed carrierUnary realSealUnary closureRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row O ∨ hsame row N ∨ hsame row carrierRead ∨ hsame row realSeal ∨
                hsame row closureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F sourceRead ∧ Cont sourceRead W graphRead ∧
              Cont graphRead E epigraphRead ∧ Cont epigraphRead O carrierRead ∧
                Cont W R windowRead ∧ Cont windowRead E thresholdRead ∧
                  Cont thresholdRead O locatedRead ∧ Cont locatedRead N realSeal ∧
                    Cont carrierRead realSeal closureRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro closureRead ⟨hsame_refl closureRead, closureUnary⟩
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
        ⟨source.right, sourceRoute, graphRoute, epigraphRoute, carrierRoute, windowRoute,
          thresholdRoute, locatedRoute, realSealRoute, closureRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, closureUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
