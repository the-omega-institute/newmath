import BedcMathlibBridge.Constructive.Eisenstein

namespace BedcMathlibBridge.Export.Eisenstein

open BedcMathlibBridge.Constructive.Eisenstein

structure EisensteinExportWitness where
  ringEquiv : CEisInt ≃+* EisensteinInt
  ring_apply : ∀ z : CEisInt, ringEquiv.toFun z = z.toEisensteinInt
  toEisensteinInt_ofEisensteinInt :
    ∀ z : EisensteinInt, (CEisInt.ofEisensteinInt z).toEisensteinInt = z
  ofEisensteinInt_toEisensteinInt :
    ∀ z : CEisInt, CEisInt.ofEisensteinInt z.toEisensteinInt = z
  add_apply : ∀ z w : CEisInt,
    (z + w).toEisensteinInt = z.toEisensteinInt + w.toEisensteinInt
  neg_apply : ∀ z : CEisInt, (-z).toEisensteinInt = -z.toEisensteinInt
  mul_apply : ∀ z w : CEisInt,
    (z * w).toEisensteinInt = z.toEisensteinInt * w.toEisensteinInt
  eisEq_apply : ∀ z w : CEisInt,
    BEDC.Derived.EisensteinUp.EisEq z.val w.val ↔
      z.toEisensteinInt = w.toEisensteinInt

def eisExport : EisensteinExportWitness where
  ringEquiv := CEisInt.toEisensteinIntRingEquiv
  ring_apply := by
    intro z
    rfl
  toEisensteinInt_ofEisensteinInt := CEisInt.toEisensteinInt_ofEisensteinInt
  ofEisensteinInt_toEisensteinInt := CEisInt.ofEisensteinInt_toEisensteinInt
  add_apply := CEisInt.toEisensteinInt_add
  neg_apply := CEisInt.toEisensteinInt_neg
  mul_apply := CEisInt.toEisensteinInt_mul
  eisEq_apply := CEisInt.eisEq_iff_toEisensteinInt_eq

theorem eis_ring_apply (z : CEisInt) :
    CEisInt.toEisensteinIntRingEquiv.toFun z = z.toEisensteinInt := by
  rfl

theorem eis_add_apply (z w : CEisInt) :
    (z + w).toEisensteinInt = z.toEisensteinInt + w.toEisensteinInt := by
  exact CEisInt.toEisensteinInt_add z w

theorem eis_neg_apply (z : CEisInt) :
    (-z).toEisensteinInt = -z.toEisensteinInt := by
  exact CEisInt.toEisensteinInt_neg z

theorem eis_mul_apply (z w : CEisInt) :
    (z * w).toEisensteinInt = z.toEisensteinInt * w.toEisensteinInt := by
  exact CEisInt.toEisensteinInt_mul z w

theorem eis_eq_apply (z w : CEisInt) :
    BEDC.Derived.EisensteinUp.EisEq z.val w.val ↔
      z.toEisensteinInt = w.toEisensteinInt := by
  exact CEisInt.eisEq_iff_toEisensteinInt_eq z w

def eis_ringEquiv_type :
    CEisInt ≃+*
      (_root_.QuadraticAlgebra _root_.Int (-1 : _root_.Int) (-1 : _root_.Int)) :=
  CEisInt.toEisensteinIntRingEquiv

end BedcMathlibBridge.Export.Eisenstein
