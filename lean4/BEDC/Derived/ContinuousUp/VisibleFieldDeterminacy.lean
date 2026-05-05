import BEDC.Derived.ContinuousUp.Suffix

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_visible_modulus_context_field_determinacy
    {p q source source' map map' target target' modulus modulus' cert cert' : BHist} :
    ((ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
          (append (append p cert) q) ->
        ContinuousFunctionCarrier (append p source) map' (append p target) (append modulus q)
          (append (append p cert) q) ->
          hsame map map') ∧
      (ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
          (append (append p cert) q) ->
        ContinuousFunctionCarrier (append p source') map (append p target) (append modulus q)
          (append (append p cert) q) ->
          hsame source source') ∧
      (ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
          (append (append p cert) q) ->
        ContinuousFunctionCarrier (append p source) map (append p target) (append modulus' q)
          (append (append p cert) q) ->
          hsame modulus modulus') ∧
      (ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
          (append (append p cert) q) ->
        ContinuousFunctionCarrier (append p source) map (append p target') (append modulus q)
          (append (append p cert') q) ->
          hsame target target' ∧ hsame cert cert')) := by
  constructor
  · intro left right
    exact ContinuousFunctionCarrier_visible_modulus_context_map_deterministic left right
  constructor
  · intro left right
    have leftData :=
      (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
        (source := source) (map := map) (target := target) (modulus := modulus)
        (cert := cert)).mp left
    have rightData :=
      (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
        (source := source') (map := map) (target := target) (modulus := modulus)
        (cert := cert)).mp right
    exact ContinuousFunctionCarrier_source_deterministic leftData.right.right rightData.right.right
  constructor
  · intro left right
    have leftData :=
      (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
        (source := source) (map := map) (target := target) (modulus := modulus)
        (cert := cert)).mp left
    have rightData :=
      (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
        (source := source) (map := map) (target := target) (modulus := modulus')
        (cert := cert)).mp right
    exact ContinuousFunctionCarrier_modulus_deterministic leftData.right.right rightData.right.right
  · intro left right
    exact ContinuousFunctionCarrier_visible_modulus_context_target_cert_deterministic left right

end BEDC.Derived.ContinuousUp
