import BEDC.Derived.IntervalDomainUp.NameCertObligations
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem IntervalDomainRegularCauchyDirectedWidthNamedReadCertificate
    {L R N W Q E H C P A dyadic earlierWidth laterWidth streamRead regseqRead
      sealRead namedRead : BHist} :
    UnaryHistory L ->
      UnaryHistory R ->
        UnaryHistory N ->
          UnaryHistory W ->
            UnaryHistory Q ->
              UnaryHistory E ->
                UnaryHistory A ->
                  UnaryHistory dyadic ->
                    Cont R dyadic earlierWidth ->
                      Cont earlierWidth N laterWidth ->
                        Cont W Q streamRead ->
                          Cont laterWidth streamRead regseqRead ->
                            Cont regseqRead E sealRead ->
                              Cont sealRead A namedRead ->
                                hsame H (append C P) ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row R ∨ hsame row N ∨ hsame row W ∨
                                          hsame row Q ∨ hsame row laterWidth ∨
                                            hsame row regseqRead ∨ hsame row sealRead ∨
                                              hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont R dyadic earlierWidth ∧
                                          Cont earlierWidth N laterWidth ∧
                                            Cont W Q streamRead ∧
                                              Cont laterWidth streamRead regseqRead ∧
                                                Cont regseqRead E sealRead ∧
                                                  Cont sealRead A namedRead ∧
                                                    hsame H (append C P))
                                      hsame ∧
                                    UnaryHistory earlierWidth ∧
                                      UnaryHistory laterWidth ∧ UnaryHistory streamRead ∧
                                        UnaryHistory regseqRead ∧ UnaryHistory sealRead ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert UnaryHistory
  intro _leftUnary rationalUnary nestedUnary streamUnary regseqUnary realSealUnary
    nameUnary dyadicUnary earlierRoute laterRoute streamRoute regseqRoute sealRoute namedRoute
    historyRoute
  have earlierUnary : UnaryHistory earlierWidth :=
    unary_cont_closed rationalUnary dyadicUnary earlierRoute
  have laterUnary : UnaryHistory laterWidth :=
    unary_cont_closed earlierUnary nestedUnary laterRoute
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed streamUnary regseqUnary streamRoute
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed laterUnary streamReadUnary regseqRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqReadUnary realSealUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row N ∨ hsame row W ∨ hsame row Q ∨
              hsame row laterWidth ∨ hsame row regseqRead ∨ hsame row sealRead ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R dyadic earlierWidth ∧ Cont earlierWidth N laterWidth ∧
              Cont W Q streamRead ∧ Cont laterWidth streamRead regseqRead ∧
                Cont regseqRead E sealRead ∧ Cont sealRead A namedRead ∧
                  hsame H (append C P))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, earlierRoute, laterRoute, streamRoute, regseqRoute, sealRoute,
          namedRoute, historyRoute⟩
  }
  exact
    ⟨cert, earlierUnary, laterUnary, streamReadUnary, regseqReadUnary, sealUnary,
      namedUnary⟩

end BEDC.Derived.IntervalDomainUp
