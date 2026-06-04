import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootEpigraphLocatedTransport [AskSetup] [PackageSetup]
    {X F E W R O H C P N W' R' E' O' windowRead windowRead' epigraphRead epigraphRead'
      locatedRead locatedRead' replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W -> UnaryHistory R -> UnaryHistory E -> UnaryHistory O -> UnaryHistory C ->
        hsame W W' -> hsame R R' -> hsame E E' -> hsame O O' ->
          Cont W R windowRead -> Cont W' R' windowRead' ->
            Cont windowRead E epigraphRead -> Cont windowRead' E' epigraphRead' ->
              Cont epigraphRead O locatedRead -> Cont epigraphRead' O' locatedRead' ->
                Cont locatedRead C replayRead -> PkgSig bundle P pkg -> PkgSig bundle N pkg ->
                  hsame locatedRead locatedRead' ∧ SemanticNameCert
                    (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W R windowRead ∧
                        Cont windowRead E epigraphRead ∧ Cont epigraphRead O locatedRead ∧
                          Cont locatedRead C replayRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle N pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields wUnary rUnary eUnary oUnary cUnary sameW sameR sameE sameO windowRoute
    windowRoute' epigraphRoute epigraphRoute' locatedRoute locatedRoute' replayRoute
    provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have sameWindow : hsame windowRead windowRead' :=
    cont_respects_hsame sameW sameR windowRoute windowRoute'
  have sameEpigraph : hsame epigraphRead epigraphRead' :=
    cont_respects_hsame sameWindow sameE epigraphRoute epigraphRoute'
  have sameLocated : hsame locatedRead locatedRead' :=
    cont_respects_hsame sameEpigraph sameO locatedRoute locatedRoute'
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed locatedUnary cUnary replayRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row H ∨
            hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row replayRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
            Cont epigraphRead O locatedRead ∧ Cont locatedRead C replayRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, epigraphRoute, locatedRoute, replayRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨sameLocated, cert⟩

end BEDC.Derived.LowerSemicontinuousUp
