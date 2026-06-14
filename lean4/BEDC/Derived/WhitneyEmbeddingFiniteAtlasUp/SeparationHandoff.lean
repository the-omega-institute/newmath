import BEDC.Derived.WhitneyEmbeddingFiniteAtlasUp.NameCertObligations

namespace BEDC.Derived.WhitneyEmbeddingFiniteAtlasUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WhitneyEmbeddingFiniteAtlasSeparationHandoff [AskSetup] [PackageSetup]
    {M K A F V S E H C P N coordinateRead vectorRead separationRead boundaryRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont A F coordinateRead ->
      Cont coordinateRead V vectorRead ->
        Cont vectorRead S separationRead ->
          Cont separationRead E boundaryRead ->
            Cont boundaryRead N namedRead ->
              PkgSig bundle P pkg ->
                UnaryHistory A ->
                  UnaryHistory F ->
                    UnaryHistory V ->
                      UnaryHistory S ->
                        UnaryHistory E ->
                          UnaryHistory N ->
                            UnaryHistory coordinateRead ∧
                              UnaryHistory vectorRead ∧
                                UnaryHistory separationRead ∧
                                  UnaryHistory boundaryRead ∧
                                    UnaryHistory namedRead ∧
                                      List.Mem (whitneyEmbeddingFiniteAtlasEncodeBHist E)
                                        (whitneyEmbeddingFiniteAtlasToEventFlow
                                          (WhitneyEmbeddingFiniteAtlasUp.mk M K A F V S E H C P N)) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro coordinateRoute vectorRoute separationRoute boundaryRoute namedRoute _pkg
    atlasUnary coordinateUnary vectorUnary separationUnary boundaryUnary nameUnary
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
  exact
    ⟨coordinateReadUnary, vectorReadUnary, separationReadUnary, boundaryReadUnary,
      namedReadUnary,
      by
        change
          List.Mem (whitneyEmbeddingFiniteAtlasEncodeBHist E)
            [whitneyEmbeddingFiniteAtlasEncodeBHist M,
              whitneyEmbeddingFiniteAtlasEncodeBHist K,
              whitneyEmbeddingFiniteAtlasEncodeBHist A,
              whitneyEmbeddingFiniteAtlasEncodeBHist F,
              whitneyEmbeddingFiniteAtlasEncodeBHist V,
              whitneyEmbeddingFiniteAtlasEncodeBHist S,
              whitneyEmbeddingFiniteAtlasEncodeBHist E,
              whitneyEmbeddingFiniteAtlasEncodeBHist H,
              whitneyEmbeddingFiniteAtlasEncodeBHist C,
              whitneyEmbeddingFiniteAtlasEncodeBHist P,
              whitneyEmbeddingFiniteAtlasEncodeBHist N]
        exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.head _))))))⟩

end BEDC.Derived.WhitneyEmbeddingFiniteAtlasUp
