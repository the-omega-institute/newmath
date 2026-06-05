import BEDC.Derived.LowerSemicontinuousUp.NameCertObligationSurface
import BEDC.Derived.LowerSemicontinuousUp.RealSealExportBoundary
import BEDC.Derived.LowerSemicontinuousUp.RootEpigraphCarrier
import BEDC.Derived.LowerSemicontinuousUp.RootEpigraphRegSeqRatHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousObligationClosureRoute [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead readbackRead epigraphRead locatedRead sealRead
      openRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory O ->
                UnaryHistory C ->
                  Cont X W windowRead ->
                    Cont windowRead R readbackRead ->
                      Cont readbackRead E epigraphRead ->
                        Cont epigraphRead O locatedRead ->
                          Cont locatedRead C sealRead ->
                            Cont epigraphRead C openRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row sealRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row X ∨ hsame row W ∨ hsame row R ∨
                                        hsame row E ∨ hsame row O ∨ hsame row C ∨
                                          hsame row sealRead ∨ hsame row openRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont X W windowRead ∧
                                        Cont windowRead R readbackRead ∧
                                          Cont readbackRead E epigraphRead ∧
                                            Cont epigraphRead O locatedRead ∧
                                              Cont locatedRead C sealRead ∧
                                                Cont epigraphRead C openRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle N pkg)
                                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields xUnary wUnary rUnary eUnary oUnary cUnary windowRoute readbackRoute
    epigraphRoute locatedRoute sealRoute openRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed xUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed readbackUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed locatedUnary cUnary sealRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                    (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, readbackRoute, epigraphRoute, locatedRoute, sealRoute,
          openRoute, provenancePkg, namePkg⟩
  }

end BEDC.Derived.LowerSemicontinuousUp
