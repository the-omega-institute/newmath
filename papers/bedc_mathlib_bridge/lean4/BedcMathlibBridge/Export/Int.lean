import BedcMathlibBridge.Constructive.Int

namespace BedcMathlibBridge.Export.Int

open BedcMathlibBridge.Constructive.Int

structure IntExportWitness where
  ringEquiv : CInt ≃+* _root_.Int
  ring_apply : ∀ x : CInt, ringEquiv.toFun x = x.toInt
  toInt_ofInt : ∀ z : _root_.Int, (CInt.ofInt z).toInt = z
  ofInt_toInt : ∀ x : CInt, CInt.ofInt x.toInt = x
  le_iff : ∀ x y : CInt, x ≤ y ↔ x.toInt ≤ y.toInt
  linearOrder : LinearOrder CInt
  dvd_iff : ∀ x y : CInt, x ∣ y ↔ x.toInt ∣ y.toInt
  add_apply : ∀ x y : CInt, (x + y).toInt = x.toInt + y.toInt
  mul_apply : ∀ x y : CInt, (x * y).toInt = x.toInt * y.toInt
  order_apply : ∀ x y : CInt, @LE.le CInt linearOrder.toLE x y ↔ x.toInt ≤ y.toInt
  dvd_apply : ∀ x y : CInt, x ∣ y ↔ x.toInt ∣ y.toInt

def cintIntExport : IntExportWitness where
  ringEquiv := CInt.toIntRingEquiv
  ring_apply := by
    intro x
    rfl
  toInt_ofInt := CInt.toInt_ofInt
  ofInt_toInt := CInt.ofInt_toInt
  le_iff := CInt.le_iff_toInt_le
  linearOrder := instLinearOrderCInt
  dvd_iff := CInt.dvd_iff_toInt_dvd
  add_apply := CInt.toInt_add
  mul_apply := CInt.toInt_mul
  order_apply := by
    intro x y
    exact CInt.le_iff_toInt_le x y
  dvd_apply := by
    intro x y
    exact CInt.dvd_iff_toInt_dvd x y

theorem cint_ring_apply (x : CInt) :
    CInt.toIntRingEquiv.toFun x = x.toInt := by
  rfl

theorem cint_add_apply (x y : CInt) :
    (x + y).toInt = x.toInt + y.toInt := by
  exact CInt.toInt_add x y

theorem cint_mul_apply (x y : CInt) :
    (x * y).toInt = x.toInt * y.toInt := by
  exact CInt.toInt_mul x y

theorem cint_order_le_iff (x y : CInt) :
    @LE.le CInt instLinearOrderCInt.toLE x y ↔ x.toInt ≤ y.toInt := by
  exact CInt.le_iff_toInt_le x y

theorem cint_dvd_iff (x y : CInt) :
    @Dvd.dvd CInt instDvdCInt x y ↔ x.toInt ∣ y.toInt := by
  exact CInt.dvd_iff_toInt_dvd x y

end BedcMathlibBridge.Export.Int
