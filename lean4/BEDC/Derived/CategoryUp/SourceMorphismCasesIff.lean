import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_source_morphism_cases_iff {a target morph : BHist} :
    CategoryHomCarrier (BHist.e1 a) target morph <->
      (morph = BHist.Empty ∧ target = BHist.e1 a ∧ UnaryHistory a) ∨
        (∃ k r : BHist,
          morph = BHist.e1 k ∧ target = BHist.e1 r ∧ UnaryHistory a ∧
            UnaryHistory k ∧ UnaryHistory r ∧ Cont (BHist.e1 a) k r) := by
  constructor
  · intro homCarrier
    exact CategoryHomCarrier_e1_source_morphism_cases homCarrier
  · intro casesData
    cases casesData with
    | inl emptyCase =>
        cases emptyCase with
        | intro morphEq rest =>
            cases rest with
            | intro targetEq sourceCarrier =>
                cases morphEq
                cases targetEq
                exact CategoryHomCarrier_empty_identity (unary_e1_closed sourceCarrier)
    | inr visibleCase =>
        cases visibleCase with
        | intro k visibleCase =>
            cases visibleCase with
            | intro r data =>
                cases data with
                | intro morphEq rest =>
                    cases rest with
                    | intro targetEq rest =>
                        cases rest with
                        | intro sourceCarrier rest =>
                            cases rest with
                            | intro morphCarrier rest =>
                                cases rest with
                                | intro targetCarrier homCont =>
                                    cases morphEq
                                    cases targetEq
                                    exact And.intro (unary_e1_closed sourceCarrier)
                                      (And.intro (unary_e1_closed targetCarrier)
                                        (And.intro (unary_e1_closed morphCarrier)
                                          (cont_step_one homCont)))

end BEDC.Derived.CategoryUp
