import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexLimitUp
open BEDC.Derived.ComplexUp

theorem complex_series_name_certificate {zero : BHist} {c : BHist -> BHist} {S : BHist}
    (conv : ComplexSeriesConv zero c S) :
    NameCert (ComplexSeriesConv zero c) ComplexHistoryClassifier := by
  exact {
    carrier_inhabited := Exists.intro S conv
    equiv_refl := by
      intro h carrier
      cases carrier with
      | intro ps rest =>
          cases rest with
          | intro N rest =>
              cases rest with
              | intro M data =>
                  exact And.intro data.right.right.left
                    (And.intro data.right.right.left (hsame_refl h))
    equiv_symm := by
      intro h k classified
      exact ComplexHistoryClassifier_symm classified
    equiv_trans := by
      intro h k r classifiedHK classifiedKR
      exact ComplexHistoryClassifier_trans classifiedHK classifiedKR
    carrier_respects_equiv := by
      intro h k classified carrier
      cases carrier with
      | intro ps rest =>
          cases rest with
          | intro N rest =>
              cases rest with
              | intro M data =>
                  exact Exists.intro ps
                    (Exists.intro N
                      (Exists.intro M
                        (And.intro data.left
                          (ComplexLimit_hsame_transport classified.right.right data.right))))
  }

end BEDC.Derived.ComplexSeriesUp
