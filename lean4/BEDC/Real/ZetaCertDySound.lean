import BEDC.Real.ZetaCertDy

set_option autoImplicit false

namespace BEDC
namespace ZetaCert
namespace Dy

structure DyIntervalSoundnessObligations where
  floorS_lower :
    (z : Int) -> floorS z * S <= z
  ceilS_upper :
    (z : Int) -> z <= ceilS z * S
  neg_sound :
    {m : Int} -> {x : I} -> MemM m x -> MemM (-m) (neg x)
  add_sound :
    {m n : Int} -> {x y : I} -> MemM m x -> MemM n y -> MemM (m + n) (add x y)
  sub_sound :
    {m n : Int} -> {x y : I} -> MemM m x -> MemM n y -> MemM (m - n) (sub x y)
  subset_sound :
    {m : Int} -> {x y : I} -> subset x y = true -> MemM m x -> MemM m y
  mul_sound :
    {m n : Int} -> {x y : I} -> MemM m x -> MemM n y -> MemProdM (m * n) (mul x y)

inductive DyMulEndpointRoundSoundnessTarget : Type
  | floorCeilMinMaxHull

end Dy
end ZetaCert
end BEDC
