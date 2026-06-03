import BEDC.Derived.CorpusSupplyDistillationUp.TasteGate

namespace BEDC.Derived.CorpusSupplyDistillationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem CorpusSupplyDistillation_mature_package_boundary
    (x : CorpusSupplyDistillationUp) :
    ∃ C F D O R H T P N : BHist,
      x = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
        FieldFaithful.fields x = [C, F, D, O, R, H, T, P, N] ∧
          Cont C F (append C F) ∧
            Cont F D (append F D) ∧
              Cont D O (append D O) ∧
                Cont O P (append O P) ∧
                  Cont P N (append P N) ∧
                    (Cont (append O P) (BHist.e0 R) O → False) ∧
                      (Cont (append O P) (BHist.e1 R) O → False) := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful BMark
  cases x with
  | mk C F D O R H T P N =>
      exact
        ⟨C, F, D, O, R, H, T, P, N, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          (fun hbad =>
            (cont_mutual_extension_right_tail_absurd
              (h := O) (k := append O P) (leftTail := P) (rightTail := R)).left rfl hbad),
          (fun hbad =>
            (cont_mutual_extension_right_tail_absurd
              (h := O) (k := append O P) (leftTail := P) (rightTail := R)).right rfl hbad)⟩

end BEDC.Derived.CorpusSupplyDistillationUp
