import BEDC.Derived.WhitneyEmbeddingFiniteAtlasUp.NameCertObligations

namespace BEDC.Derived.WhitneyEmbeddingFiniteAtlasUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WhitneyEmbeddingFiniteAtlasNonescape [AskSetup] [PackageSetup]
    {M K A F V S E H C P N coordinateRead vectorRead separationRead boundaryRead namedRead
      outsider : BHist}
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
                            hsame outsider M ∨ hsame outsider K ∨ hsame outsider A ∨
                              hsame outsider F ∨ hsame outsider V ∨ hsame outsider S ∨
                                hsame outsider E ∨ hsame outsider H ∨ hsame outsider C ∨
                                  hsame outsider P ∨ hsame outsider N ->
                              List.Mem (whitneyEmbeddingFiniteAtlasEncodeBHist outsider)
                                  (whitneyEmbeddingFiniteAtlasToEventFlow
                                    (WhitneyEmbeddingFiniteAtlasUp.mk M K A F V S E H C P N)) ∨
                                hsame outsider namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro _coordinateRoute _vectorRoute _separationRoute _boundaryRoute _namedRoute _pkg
    _atlasUnary _coordinateUnary _vectorUnary _separationUnary _boundaryUnary _nameUnary displayed
  change
    List.Mem (whitneyEmbeddingFiniteAtlasEncodeBHist outsider)
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
          whitneyEmbeddingFiniteAtlasEncodeBHist N] ∨
      hsame outsider namedRead
  cases displayed with
  | inl hM =>
      cases hM
      exact Or.inl (List.Mem.head _)
  | inr restM =>
      cases restM with
      | inl hK =>
          cases hK
          exact Or.inl (List.Mem.tail _ (List.Mem.head _))
      | inr restK =>
          cases restK with
          | inl hA =>
              cases hA
              exact Or.inl (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
          | inr restA =>
              cases restA with
              | inl hF =>
                  cases hF
                  exact
                    Or.inl
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.head _))))
              | inr restF =>
                  cases restF with
                  | inl hV =>
                      cases hV
                      exact
                        Or.inl
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.head _)))))
                  | inr restV =>
                      cases restV with
                      | inl hS =>
                          cases hS
                          exact
                            Or.inl
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.tail _
                                    (List.Mem.tail _
                                      (List.Mem.tail _
                                        (List.Mem.head _))))))
                      | inr restS =>
                          cases restS with
                          | inl hE =>
                              cases hE
                              exact
                                Or.inl
                                  (List.Mem.tail _
                                    (List.Mem.tail _
                                      (List.Mem.tail _
                                        (List.Mem.tail _
                                          (List.Mem.tail _
                                            (List.Mem.tail _
                                              (List.Mem.head _)))))))
                          | inr restE =>
                              cases restE with
                              | inl hH =>
                                  cases hH
                                  exact
                                    Or.inl
                                      (List.Mem.tail _
                                        (List.Mem.tail _
                                          (List.Mem.tail _
                                            (List.Mem.tail _
                                              (List.Mem.tail _
                                                (List.Mem.tail _
                                                  (List.Mem.tail _
                                                    (List.Mem.head _))))))))
                              | inr restH =>
                                  cases restH with
                                  | inl hC =>
                                      cases hC
                                      exact
                                        Or.inl
                                          (List.Mem.tail _
                                            (List.Mem.tail _
                                              (List.Mem.tail _
                                                (List.Mem.tail _
                                                  (List.Mem.tail _
                                                    (List.Mem.tail _
                                                      (List.Mem.tail _
                                                        (List.Mem.tail _
                                                          (List.Mem.head _)))))))))
                                  | inr restC =>
                                      cases restC with
                                      | inl hP =>
                                          cases hP
                                          exact
                                            Or.inl
                                              (List.Mem.tail _
                                                (List.Mem.tail _
                                                  (List.Mem.tail _
                                                    (List.Mem.tail _
                                                      (List.Mem.tail _
                                                        (List.Mem.tail _
                                                          (List.Mem.tail _
                                                            (List.Mem.tail _
                                                              (List.Mem.tail _
                                                                (List.Mem.head _))))))))))
                                      | inr hN =>
                                          cases hN
                                          exact
                                            Or.inl
                                              (List.Mem.tail _
                                                (List.Mem.tail _
                                                  (List.Mem.tail _
                                                    (List.Mem.tail _
                                                      (List.Mem.tail _
                                                        (List.Mem.tail _
                                                          (List.Mem.tail _
                                                            (List.Mem.tail _
                                                              (List.Mem.tail _
                                                                (List.Mem.tail _
                                                                  (List.Mem.head _)))))))))))

end BEDC.Derived.WhitneyEmbeddingFiniteAtlasUp
