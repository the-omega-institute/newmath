import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp

theorem complex_limit_name_certificate :
    NameCert
      (fun h : BHist =>
        exists s : BHist -> BHist, exists N : BHist -> BHist, exists M : BHist -> BHist,
          ComplexLimit s N h M)
      hsame := by
  have ratUnit : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_iff_positive_denominator.mpr
      (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
  have originCarrier : ComplexHistoryCarrier
      (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)) :=
    ProdHistoryCarrier_append_intro ratUnit ratUnit
  constructor
  · exact Exists.intro (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
      (Exists.intro (fun _ : BHist => append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
        (Exists.intro (fun _ : BHist => BHist.Empty)
          (Exists.intro (fun _ : BHist => BHist.Empty)
            (ComplexLimit_constant originCarrier))))
  · intro h _source
    exact hsame_refl h
  · intro h k sameHK
    exact hsame_symm sameHK
  · intro h k r sameHK sameKR
    exact hsame_trans sameHK sameKR
  · intro h k sameHK source
    cases source with
    | intro s rest =>
        cases rest with
        | intro N rest =>
            cases rest with
            | intro M limit =>
                exact Exists.intro s
                  (Exists.intro N
                  (Exists.intro M
                      (ComplexLimit_hsame_transport sameHK limit)))

theorem complex_limit_semantic_name_certificate :
    SemanticNameCert
      (fun h : BHist => exists s : BHist -> BHist, exists N : BHist -> BHist,
        exists M : BHist -> BHist, ComplexLimit s N h M)
      (fun h : BHist => exists s : BHist -> BHist, exists N : BHist -> BHist,
        exists M : BHist -> BHist, ComplexLimit s N h M)
      (fun h : BHist => exists s : BHist -> BHist, exists N : BHist -> BHist,
        exists M : BHist -> BHist, ComplexLimit s N h M)
      (fun h k : BHist =>
        (exists s : BHist -> BHist, exists N : BHist -> BHist,
          exists M : BHist -> BHist, ComplexLimit s N h M) ∧
        (exists s : BHist -> BHist, exists N : BHist -> BHist,
          exists M : BHist -> BHist, ComplexLimit s N k M) ∧ hsame h k) := by
  cases complex_history_semantic_name_certificate.core.carrier_inhabited with
  | intro z carrierZ =>
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro z
              (Exists.intro (fun _ : BHist => z)
                (Exists.intro (fun _ : BHist => BHist.Empty)
                  (Exists.intro (fun _ : BHist => BHist.Empty)
                    (ComplexLimit_constant carrierZ))))
          equiv_refl := by
            intro h source
            exact And.intro source (And.intro source (hsame_refl h))
          equiv_symm := by
            intro h k classified
            exact And.intro classified.right.left
              (And.intro classified.left (hsame_symm classified.right.right))
          equiv_trans := by
            intro h k r classifiedHK classifiedKR
            exact And.intro classifiedHK.left
              (And.intro classifiedKR.right.left
                (hsame_trans classifiedHK.right.right classifiedKR.right.right))
          carrier_respects_equiv := by
            intro h k classified _sourceH
            exact classified.right.left
        }
        pattern_sound := by
          intro h source
          exact source
        ledger_sound := by
          intro h source
          exact source
      }

end BEDC.Derived.ComplexLimitUp
