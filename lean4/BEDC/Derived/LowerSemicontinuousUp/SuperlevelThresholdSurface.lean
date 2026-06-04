import BEDC.Derived.LowerSemicontinuousUp.RealHandoff
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
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

def LowerSemicontinuousSuperlevelThresholdSurface [AskSetup] [PackageSetup]
    (threshold epigraph located boundary transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  UnaryHistory threshold ∧
    UnaryHistory epigraph ∧
      UnaryHistory located ∧
        UnaryHistory boundary ∧
          UnaryHistory transport ∧
            UnaryHistory replay ∧
              UnaryHistory provenance ∧
                UnaryHistory localName ∧
                  Cont epigraph located boundary ∧
                    Cont boundary transport replay ∧
                      hsame transport localName ∧ PkgSig bundle provenance pkg

theorem LowerSemicontinuousSuperlevelThresholdSurface_threshold_route [AskSetup]
    [PackageSetup]
    {threshold epigraph located boundary transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LowerSemicontinuousSuperlevelThresholdSurface threshold epigraph located boundary
        transport replay provenance localName bundle pkg →
      UnaryHistory threshold ∧ Cont epigraph located boundary ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro surface
  exact ⟨surface.left, surface.right.right.right.right.right.right.right.right.left,
    surface.right.right.right.right.right.right.right.right.right.right.right⟩

def lowerSemicontinuousSuperlevelThresholdSurface
    (q Eq Oq Bq Hq Cq Pq Nq : BHist) : List BHist :=
  [q, Eq, Oq, Bq, Hq, Cq, Pq, Nq]

theorem LowerSemicontinuousSuperlevelThresholdSurface_exact [AskSetup] [PackageSetup]
    {q Eq Oq Bq Hq Cq Pq Nq thresholdRead boundaryRead stableRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousSuperlevelThresholdSurface q Eq Oq Bq Hq Cq Pq Nq =
        [q, Eq, Oq, Bq, Hq, Cq, Pq, Nq] →
      UnaryHistory q →
        UnaryHistory Eq →
          UnaryHistory Oq →
            UnaryHistory Bq →
              UnaryHistory Hq →
                Cont q Eq thresholdRead →
                  Cont thresholdRead Oq boundaryRead →
                    Cont boundaryRead Bq stableRead →
                      Cont stableRead Hq replayRead →
                        PkgSig bundle Pq pkg →
                          PkgSig bundle Nq pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row q ∨ hsame row Eq ∨ hsame row Oq ∨
                                    hsame row Bq ∨ hsame row Hq ∨ hsame row replayRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont q Eq thresholdRead ∧
                                    Cont thresholdRead Oq boundaryRead ∧
                                      Cont boundaryRead Bq stableRead ∧
                                        Cont stableRead Hq replayRead ∧
                                          PkgSig bundle Pq pkg ∧ PkgSig bundle Nq pkg)
                                hsame ∧
                              UnaryHistory thresholdRead ∧ UnaryHistory boundaryRead ∧
                                UnaryHistory stableRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fieldRows qUnary eqUnary oqUnary bqUnary hqUnary thresholdRoute boundaryRoute
    stableRoute replayRoute pPkg nPkg
  cases fieldRows
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed qUnary eqUnary thresholdRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed thresholdUnary oqUnary boundaryRoute
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed boundaryUnary bqUnary stableRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed stableUnary hqUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row Eq ∨ hsame row Oq ∨ hsame row Bq ∨
              hsame row Hq ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q Eq thresholdRead ∧
              Cont thresholdRead Oq boundaryRead ∧ Cont boundaryRead Bq stableRead ∧
                Cont stableRead Hq replayRead ∧ PkgSig bundle Pq pkg ∧
                  PkgSig bundle Nq pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, thresholdRoute, boundaryRoute, stableRoute, replayRoute, pPkg, nPkg⟩
  }
  exact ⟨cert, thresholdUnary, boundaryUnary, stableUnary, replayUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
