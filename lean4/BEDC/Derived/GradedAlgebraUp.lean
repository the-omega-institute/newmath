import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.GradedAlgebraUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def GradedAlgebraBHistSource (row : BHist) : Prop :=
  exists base degree component product provenance : BHist,
    Cont base degree component ∧
      Cont component product provenance ∧ hsame row (BHist.e0 provenance)

def GradedAlgebraDegreePattern (row : BHist) : Prop :=
  exists base degree component provenance : BHist,
    Cont base degree component ∧ hsame row (BHist.e0 provenance)

def GradedAlgebraProductLedger (row : BHist) : Prop :=
  exists component product provenance : BHist,
    Cont component product provenance ∧ hsame row (BHist.e0 provenance)

theorem GradedAlgebraPacket_namecert_obligation_surface :
    SemanticNameCert GradedAlgebraBHistSource GradedAlgebraDegreePattern
      GradedAlgebraProductLedger hsame := by
  have source : GradedAlgebraBHistSource (BHist.e0 BHist.Empty) := by
    exact Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (Exists.intro BHist.Empty
            (Exists.intro BHist.Empty
              (And.intro (cont_left_unit BHist.Empty)
                (And.intro (cont_left_unit BHist.Empty)
                  (hsame_refl (BHist.e0 BHist.Empty))))))))
  constructor
  · constructor
    · exact Exists.intro (BHist.e0 BHist.Empty) source
    · intro row _source
      exact hsame_refl row
    · intro left right sameRows
      exact hsame_symm sameRows
    · intro left middle right sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro left right sameRows sourceLeft
      cases sourceLeft with
      | intro base baseData =>
          cases baseData with
          | intro degree degreeData =>
              cases degreeData with
              | intro component componentData =>
                  cases componentData with
                  | intro product productData =>
                      cases productData with
                      | intro provenance packet =>
                          exact Exists.intro base
                            (Exists.intro degree
                              (Exists.intro component
                                (Exists.intro product
                                  (Exists.intro provenance
                                    (And.intro packet.left
                                      (And.intro packet.right.left
                                        (hsame_trans (hsame_symm sameRows)
                                          packet.right.right)))))))
  · intro row sourceRow
    cases sourceRow with
    | intro base baseData =>
        cases baseData with
        | intro degree degreeData =>
            cases degreeData with
            | intro component componentData =>
                cases componentData with
                | intro product productData =>
                    cases productData with
                    | intro provenance packet =>
                        exact Exists.intro base
                          (Exists.intro degree
                            (Exists.intro component
                              (Exists.intro provenance
                                (And.intro packet.left packet.right.right))))
  · intro row sourceRow
    cases sourceRow with
    | intro base baseData =>
        cases baseData with
        | intro degree degreeData =>
            cases degreeData with
            | intro component componentData =>
                cases componentData with
                | intro product productData =>
                    cases productData with
                    | intro provenance packet =>
                        exact Exists.intro component
                          (Exists.intro product
                            (Exists.intro provenance
                              (And.intro packet.right.left packet.right.right)))

end BEDC.Derived.GradedAlgebraUp
