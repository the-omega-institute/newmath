import BEDC.Derived.LowerSemicontinuousUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousSuperlevelTailObligation [AskSetup] [PackageSetup]
    {q Eq Oq Bq Hq Cq Pq Nq thresholdRead boundaryRead stableRead replayRead
      exhaustedRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q ->
      UnaryHistory Eq ->
        UnaryHistory Oq ->
          UnaryHistory Bq ->
            UnaryHistory Hq ->
              UnaryHistory Cq ->
                UnaryHistory Nq ->
                  Cont q Eq thresholdRead ->
                    Cont thresholdRead Oq boundaryRead ->
                      Cont boundaryRead Bq stableRead ->
                        Cont stableRead Hq replayRead ->
                          Cont replayRead Cq exhaustedRead ->
                            Cont exhaustedRead Nq tailRead ->
                              PkgSig bundle Pq pkg ->
                                PkgSig bundle Nq pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row q ∨ hsame row Eq ∨ hsame row Oq ∨
                                          hsame row Bq ∨ hsame row Hq ∨ hsame row Cq ∨
                                            hsame row Pq ∨ hsame row Nq ∨
                                              hsame row exhaustedRead ∨ hsame row tailRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont q Eq thresholdRead ∧
                                          Cont thresholdRead Oq boundaryRead ∧
                                            Cont boundaryRead Bq stableRead ∧
                                              Cont stableRead Hq replayRead ∧
                                                Cont replayRead Cq exhaustedRead ∧
                                                  Cont exhaustedRead Nq tailRead ∧
                                                    PkgSig bundle Pq pkg ∧
                                                      PkgSig bundle Nq pkg)
                                      hsame ∧
                                    UnaryHistory tailRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryQ unaryEq unaryOq unaryBq unaryHq unaryCq unaryNq thresholdRoute
    boundaryRoute stableRoute replayRoute exhaustedRoute tailRoute provenancePkg namePkg
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryQ unaryEq thresholdRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed thresholdUnary unaryOq boundaryRoute
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed boundaryUnary unaryBq stableRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed stableUnary unaryHq replayRoute
  have exhaustedUnary : UnaryHistory exhaustedRead :=
    unary_cont_closed replayUnary unaryCq exhaustedRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed exhaustedUnary unaryNq tailRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row Eq ∨ hsame row Oq ∨ hsame row Bq ∨ hsame row Hq ∨
              hsame row Cq ∨ hsame row Pq ∨ hsame row Nq ∨ hsame row exhaustedRead ∨
                hsame row tailRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q Eq thresholdRead ∧
              Cont thresholdRead Oq boundaryRead ∧ Cont boundaryRead Bq stableRead ∧
                Cont stableRead Hq replayRead ∧ Cont replayRead Cq exhaustedRead ∧
                  Cont exhaustedRead Nq tailRead ∧ PkgSig bundle Pq pkg ∧
                    PkgSig bundle Nq pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro tailRead ⟨hsame_refl tailRead, tailUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, thresholdRoute, boundaryRoute, stableRoute, replayRoute,
          exhaustedRoute, tailRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, tailUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
