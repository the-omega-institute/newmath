import BedcMathlibBridge.Constructive.Gaussian

namespace BedcMathlibBridge.Export.Gaussian

open BedcMathlibBridge.Constructive.Gaussian

structure GaussianExportWitness where
  ringEquiv : CGaussInt ≃+* _root_.GaussianInt
  ring_apply : ∀ z : CGaussInt, ringEquiv.toFun z = z.toGaussianInt
  toGaussianInt_ofGaussianInt :
    ∀ z : _root_.GaussianInt, (CGaussInt.ofGaussianInt z).toGaussianInt = z
  ofGaussianInt_toGaussianInt :
    ∀ z : CGaussInt, CGaussInt.ofGaussianInt z.toGaussianInt = z
  add_apply : ∀ z w : CGaussInt,
    (z + w).toGaussianInt = z.toGaussianInt + w.toGaussianInt
  neg_apply : ∀ z : CGaussInt, (-z).toGaussianInt = -z.toGaussianInt
  mul_apply : ∀ z w : CGaussInt,
    (z * w).toGaussianInt = z.toGaussianInt * w.toGaussianInt
  zero_apply : (0 : CGaussInt).toGaussianInt = 0
  one_apply : (1 : CGaussInt).toGaussianInt = 1
  gaussEq_apply : ∀ z w : CGaussInt,
    BEDC.Derived.GaussianUp.GaussEq z.val w.val ↔
      z.toGaussianInt = w.toGaussianInt

def gaussExport : GaussianExportWitness where
  ringEquiv := CGaussInt.toGaussianIntRingEquiv
  ring_apply := by
    intro z
    rfl
  toGaussianInt_ofGaussianInt := CGaussInt.toGaussianInt_ofGaussianInt
  ofGaussianInt_toGaussianInt := CGaussInt.ofGaussianInt_toGaussianInt
  add_apply := CGaussInt.toGaussianInt_add
  neg_apply := CGaussInt.toGaussianInt_neg
  mul_apply := CGaussInt.toGaussianInt_mul
  zero_apply := CGaussInt.toGaussianInt_zero
  one_apply := CGaussInt.toGaussianInt_one
  gaussEq_apply := CGaussInt.gaussEq_iff_toGaussianInt_eq

theorem gauss_ring_apply (z : CGaussInt) :
    CGaussInt.toGaussianIntRingEquiv.toFun z = z.toGaussianInt := by
  rfl

theorem gauss_add_apply (z w : CGaussInt) :
    (z + w).toGaussianInt = z.toGaussianInt + w.toGaussianInt := by
  exact CGaussInt.toGaussianInt_add z w

theorem gauss_neg_apply (z : CGaussInt) :
    (-z).toGaussianInt = -z.toGaussianInt := by
  exact CGaussInt.toGaussianInt_neg z

theorem gauss_mul_apply (z w : CGaussInt) :
    (z * w).toGaussianInt = z.toGaussianInt * w.toGaussianInt := by
  exact CGaussInt.toGaussianInt_mul z w

theorem gauss_zero_apply :
    (0 : CGaussInt).toGaussianInt = 0 := by
  exact CGaussInt.toGaussianInt_zero

theorem gauss_one_apply :
    (1 : CGaussInt).toGaussianInt = 1 := by
  exact CGaussInt.toGaussianInt_one

theorem gauss_eq_apply (z w : CGaussInt) :
    BEDC.Derived.GaussianUp.GaussEq z.val w.val ↔
      z.toGaussianInt = w.toGaussianInt := by
  exact CGaussInt.gaussEq_iff_toGaussianInt_eq z w

def gauss_ringEquiv_type :
    CGaussInt ≃+* _root_.GaussianInt :=
  gaussExport.ringEquiv

end BedcMathlibBridge.Export.Gaussian
