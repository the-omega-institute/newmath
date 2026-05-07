import BEDC.Derived.LieAlgebraUp
import BEDC.Derived.LieGroupUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ExpMapUp

open BEDC.Derived.LieAlgebraUp
open BEDC.Derived.LieGroupUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ExpMapGraphCarrier_obligation_surface {tangent flow endpoint : BHist} :
    LieAlgebraSingletonCarrier tangent ->
      LieGroupSingletonCarrier endpoint ->
        Cont tangent flow endpoint ->
          SemanticNameCert
              (fun row : BHist =>
                LieAlgebraSingletonCarrier tangent ∧ Cont tangent flow row ∧
                  LieGroupSingletonCarrier row)
              (fun row : BHist =>
                LieAlgebraSingletonCarrier tangent ∧ Cont tangent flow row ∧
                  LieGroupSingletonCarrier row)
              (fun row : BHist =>
                LieAlgebraSingletonCarrier tangent ∧ Cont tangent flow row ∧
                  LieGroupSingletonCarrier row)
              hsame ∧
            UnaryHistory endpoint := by
  intro tangentCarrier endpointCarrier endpointRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport unary_empty (hsame_symm endpointCarrier)
  constructor
  · constructor
    · constructor
      · exact Exists.intro endpoint (And.intro tangentCarrier (And.intro endpointRow endpointCarrier))
      · intro row _carrier
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same carrier
        exact And.intro carrier.left
          (And.intro (cont_result_hsame_transport carrier.right.left same)
            (hsame_trans (hsame_symm same) carrier.right.right))
    · intro _row source
      exact source
    · intro _row source
      exact source
  · exact endpointUnary

end BEDC.Derived.ExpMapUp
