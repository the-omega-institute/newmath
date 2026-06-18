import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopCompletionComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionComparisonNameCertObligations [AskSetup] [PackageSetup]
    {regular boundary locatedLimit locatedReal realSeal replayToBoundary replayToLimit
      replayToLocated provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory regular ->
      UnaryHistory boundary ->
        UnaryHistory locatedLimit ->
          UnaryHistory locatedReal ->
            UnaryHistory localName ->
              Cont regular boundary replayToBoundary ->
                Cont replayToBoundary locatedLimit replayToLimit ->
                  Cont replayToLimit locatedReal replayToLocated ->
                    Cont replayToLocated localName realSeal ->
                      PkgSig bundle provenance pkg ->
                        PkgSig bundle realSeal pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row regular ∨ hsame row boundary ∨
                                  hsame row locatedLimit ∨ hsame row locatedReal ∨
                                    hsame row realSeal ∨ hsame row provenance)
                              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle realSeal pkg)
                              hsame ∧
                            UnaryHistory replayToBoundary ∧ UnaryHistory replayToLimit ∧
                              UnaryHistory replayToLocated ∧ UnaryHistory realSeal ∧
                                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro regularUnary boundaryUnary locatedLimitUnary locatedRealUnary localNameUnary
    boundaryRoute limitRoute locatedRoute sealRoute provenancePkg realSealPkg
  have replayBoundaryUnary : UnaryHistory replayToBoundary :=
    unary_cont_closed regularUnary boundaryUnary boundaryRoute
  have replayLimitUnary : UnaryHistory replayToLimit :=
    unary_cont_closed replayBoundaryUnary locatedLimitUnary limitRoute
  have replayLocatedUnary : UnaryHistory replayToLocated :=
    unary_cont_closed replayLimitUnary locatedRealUnary locatedRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed replayLocatedUnary localNameUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row regular ∨ hsame row boundary ∨ hsame row locatedLimit ∨
              hsame row locatedReal ∨ hsame row realSeal ∨ hsame row provenance)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realSealPkg⟩
  }
  exact
    ⟨cert, replayBoundaryUnary, replayLimitUnary, replayLocatedUnary, realSealUnary,
      provenancePkg⟩

end BEDC.Derived.BishopCompletionComparisonUp
