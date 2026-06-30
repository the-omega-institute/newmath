import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.ZetaCosmosClosure

namespace BEDC.Derived.RHRoute.ZetaUnitaryScaleClosure

open BEDC.Derived.RHRoute.ConstructiveRHStatement

structure GoldenScaleEigenvalue (s : RatComplex) where
  centered_source : RatComplex
  modulus_unit : Prop
  modulus_identity : Prop
  critical_line_iff_unit_modulus : modulus_unit -> OnCriticalLine s

structure ZetaUnitaryScaleClosure where
  no_independent_real_scale_ledger :
    (s : RatComplex) -> NontrivialZetaZero s -> Prop
  golden_scale : (s : RatComplex) -> GoldenScaleEigenvalue s
  no_scale_to_unitary :
    (s : RatComplex) -> (h : NontrivialZetaZero s) ->
      no_independent_real_scale_ledger s h ->
        (golden_scale s).modulus_unit
  zero_packets_have_no_scale :
    (s : RatComplex) -> (h : NontrivialZetaZero s) ->
      no_independent_real_scale_ledger s h

theorem rh_via_unitary_scale_closure
    (closure : ZetaUnitaryScaleClosure) :
    ConstructiveRH := by
  intro s zeroPacket
  exact
    (closure.golden_scale s).critical_line_iff_unit_modulus
      (closure.no_scale_to_unitary s zeroPacket
        (closure.zero_packets_have_no_scale s zeroPacket))

end BEDC.Derived.RHRoute.ZetaUnitaryScaleClosure
