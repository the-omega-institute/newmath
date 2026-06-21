import BEDC.FKernel.Mark
import BedcMathlibBridge.Core.RelEquiv

namespace BedcMathlibBridge.Constructive.Bool

open BEDC.FKernel.Mark

def toBool : BMark → Bool
  | BMark.b0 => false
  | BMark.b1 => true

def ofBool : Bool → BMark
  | false => BMark.b0
  | true => BMark.b1

theorem toBool_b0 : toBool BMark.b0 = false := by
  rfl

theorem toBool_b1 : toBool BMark.b1 = true := by
  rfl

theorem ofBool_toBool : ∀ m : BMark, ofBool (toBool m) = m := by
  intro m
  cases m with
  | b0 =>
      rfl
  | b1 =>
      rfl

theorem toBool_ofBool : ∀ b : Bool, toBool (ofBool b) = b := by
  intro b
  cases b with
  | false =>
      rfl
  | true =>
      rfl

theorem toBool_eq_of_msame {m n : BMark} : msame m n → toBool m = toBool n := by
  intro h
  cases h
  rfl

theorem msame_of_toBool_eq {m n : BMark} : toBool m = toBool n → msame m n := by
  intro h
  cases m with
  | b0 =>
      cases n with
      | b0 =>
          rfl
      | b1 =>
          exact Bool.noConfusion h
  | b1 =>
      cases n with
      | b0 =>
          exact Bool.noConfusion h
      | b1 =>
          rfl

theorem msame_iff_toBool_eq (m n : BMark) : msame m n ↔ toBool m = toBool n := by
  constructor
  · exact toBool_eq_of_msame
  · exact msame_of_toBool_eq

def bmarkBoolRelEquiv : BedcMathlibBridge.RelEquiv BMark msame Bool where
  toM := toBool
  ofM := ofBool
  leftInv := ofBool_toBool
  rightInv := toBool_ofBool
  relIff := msame_iff_toBool_eq

def bmarkBoolEquiv : BMark ≃ Bool :=
  bmarkBoolRelEquiv.toEquiv

#print axioms bmarkBoolEquiv
#print axioms bmarkBoolRelEquiv
#print axioms msame_iff_toBool_eq

end BedcMathlibBridge.Constructive.Bool
