import BEDC.Derived.FieldUp
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem RatupFieldupAssembledSupportNeutralityCertificate
    {h inner collected k s t s' t' : BHist} :
    Cont h (append s t) inner ->
      Cont h (append s' t') collected ->
        hsame s BHist.Empty ->
          hsame t BHist.Empty ->
            hsame s' BHist.Empty ->
              hsame t' BHist.Empty ->
                hsame k collected ->
                  UnaryHistory h ->
                    UnaryHistory inner ∧ UnaryHistory collected ∧ hsame inner h ∧
                      hsame collected h ∧ hsame k h := by
  intro innerRow collectedRow sameS sameT sameS' sameT' sameKCollected unaryH
  cases sameS
  cases sameT
  cases sameS'
  cases sameT'
  have innerSameH : hsame inner h := cont_right_unit_result innerRow
  have collectedSameH : hsame collected h := cont_right_unit_result collectedRow
  have innerUnary : UnaryHistory inner := unary_transport unaryH (hsame_symm innerSameH)
  have collectedUnary : UnaryHistory collected := unary_transport unaryH (hsame_symm collectedSameH)
  have kSameH : hsame k h := hsame_trans sameKCollected collectedSameH
  exact ⟨innerUnary, collectedUnary, innerSameH, collectedSameH, kSameH⟩

end BEDC.Derived.FieldUp
