import BEDC.Derived.WhitneyEmbeddingFiniteAtlasUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WhitneyEmbeddingFiniteAtlasUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WhitneyEmbeddingFiniteAtlasNameCertObligations [AskSetup] [PackageSetup]
    {M K A F V S E H C P N coordinateRead vectorRead separationRead boundaryRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory K ->
        UnaryHistory A ->
          UnaryHistory F ->
            UnaryHistory V ->
              UnaryHistory S ->
                UnaryHistory E ->
                  UnaryHistory H ->
                    UnaryHistory C ->
                      UnaryHistory P ->
                        UnaryHistory N ->
                          Cont A F coordinateRead ->
                            Cont coordinateRead V vectorRead ->
                              Cont vectorRead S separationRead ->
                                Cont separationRead E boundaryRead ->
                                  Cont boundaryRead N namedRead ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle namedRead pkg ->
                                        SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row M ∨ hsame row K ∨ hsame row A ∨
                                              hsame row F ∨ hsame row V ∨ hsame row S ∨
                                                hsame row E ∨ hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont A F coordinateRead ∧
                                              Cont coordinateRead V vectorRead ∧
                                                Cont vectorRead S separationRead ∧
                                                  Cont separationRead E boundaryRead ∧
                                                    Cont boundaryRead N namedRead ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle namedRead pkg)
                                          hsame ∧ UnaryHistory coordinateRead ∧
                                            UnaryHistory vectorRead ∧ UnaryHistory separationRead ∧
                                              UnaryHistory boundaryRead ∧
                                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _manifoldUnary _compactUnary atlasUnary coordinateUnary vectorUnary separationUnary
    boundaryUnary _transportUnary _continuationUnary _provenanceUnary nameUnary
    coordinateRoute vectorRoute separationRoute boundaryRoute namedRoute provenancePkg namedPkg
  have coordinateReadUnary : UnaryHistory coordinateRead :=
    unary_cont_closed atlasUnary coordinateUnary coordinateRoute
  have vectorReadUnary : UnaryHistory vectorRead :=
    unary_cont_closed coordinateReadUnary vectorUnary vectorRoute
  have separationReadUnary : UnaryHistory separationRead :=
    unary_cont_closed vectorReadUnary separationUnary separationRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed separationReadUnary boundaryUnary boundaryRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed boundaryReadUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row K ∨ hsame row A ∨ hsame row F ∨ hsame row V ∨
            hsame row S ∨ hsame row E ∨ hsame row namedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont A F coordinateRead ∧ Cont coordinateRead V vectorRead ∧
            Cont vectorRead S separationRead ∧ Cont separationRead E boundaryRead ∧
              Cont boundaryRead N namedRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle namedRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coordinateRoute, vectorRoute, separationRoute, boundaryRoute,
          namedRoute, provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, coordinateReadUnary, vectorReadUnary, separationReadUnary, boundaryReadUnary,
      namedReadUnary⟩

end BEDC.Derived.WhitneyEmbeddingFiniteAtlasUp
