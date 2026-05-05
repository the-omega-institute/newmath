import BEDC.Derived.RatUp

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem RatClassifierSpec_representative_stability_package
    {normalized : BMark -> BHist -> BHist -> Prop}
    {s1 s2 s3 t1 t2 : BMark} {n1 n2 n3 n1' n2' d1 d2 d3 d1' d2' : BHist} :
    RatSourceSpec normalized s1 n1 d1 ->
      RatClassifierSpec s1 n1 d1 s2 n2 d2 ->
        RatClassifierSpec s2 n2 d2 s3 n3 d3 ->
          msame s1 t1 ->
            msame s2 t2 ->
              hsame n1 n1' ->
                hsame n2 n2' ->
                  hsame d1 d1' ->
                    hsame d2 d2' ->
                      RatCarrier s1 n1 d1 ∧
                        RatClassifierSpec s1 n1 d1 s1 n1 d1 ∧
                          RatClassifierSpec s2 n2 d2 s1 n1 d1 ∧
                            RatClassifierSpec s1 n1 d1 s3 n3 d3 ∧
                              RatClassifierSpec t1 n1' d1' t2 n2' d2' := by
  intro source classifier12 classifier23 sameS1 sameS2 sameN1 sameN2 sameD1 sameD2
  have carrier1 : RatCarrier s1 n1 d1 := RatSourceSpec_to_RatCarrier source
  have refl1 : RatClassifierSpec s1 n1 d1 s1 n1 d1 :=
    RatClassifierSpec_refl carrier1
  have symm21 : RatClassifierSpec s2 n2 d2 s1 n1 d1 :=
    RatClassifierSpec_symm classifier12
  have trans13 : RatClassifierSpec s1 n1 d1 s3 n3 d3 :=
    RatClassifierSpec_trans classifier12 classifier23
  have transported : RatClassifierSpec t1 n1' d1' t2 n2' d2' :=
    RatClassifierSpec_component_transport classifier12 sameS1 sameS2 sameN1 sameN2 sameD1
      sameD2
  exact ⟨carrier1, refl1, symm21, trans13, transported⟩

end BEDC.Derived.RatUp
