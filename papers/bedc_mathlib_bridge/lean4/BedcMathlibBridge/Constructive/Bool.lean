import BEDC.Derived.BoolUp.StdBridge
import BedcMathlibBridge.Adapter.MathlibEquiv

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

theorem toBool_b0_ne_b1 : toBool BMark.b0 ≠ toBool BMark.b1 := by
  intro h
  exact Bool.noConfusion h

theorem not_msame_b0_b1_via_bridge : ¬ msame BMark.b0 BMark.b1 := by
  exact not_msame_b0_b1

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

end BedcMathlibBridge.Constructive.Bool

namespace BedcMathlibBridge.Constructive.Bool.BoolUp

open BEDC.Derived.BoolUp
open BEDC.FKernel.Mark

abbrev CBool : Type :=
  BoolCarrier

def toBool : CBool → Bool
  | BMark.b0 => false
  | BMark.b1 => true

def ofBool : Bool → CBool
  | false => BMark.b0
  | true => BMark.b1

theorem toBool_b0 : toBool BMark.b0 = false := by
  rfl

theorem toBool_b1 : toBool BMark.b1 = true := by
  rfl

theorem ofBool_toBool (b : CBool) : ofBool (toBool b) = b := by
  cases b with
  | b0 =>
      rfl
  | b1 =>
      rfl

theorem toBool_ofBool (b : Bool) : toBool (ofBool b) = b := by
  cases b with
  | false =>
      rfl
  | true =>
      rfl

theorem classifier_iff_toBool_eq (b c : CBool) :
    BoolClassifierSpec b c ↔ toBool b = toBool c := by
  cases b with
  | b0 =>
      cases c with
      | b0 =>
          constructor
          · intro _
            rfl
          · intro _
            exact msame_refl BMark.b0
      | b1 =>
          constructor
          · intro h
            exact False.elim (not_msame_b0_b1 h)
          · intro h
            exact False.elim (Bool.noConfusion h)
  | b1 =>
      cases c with
      | b0 =>
          constructor
          · intro h
            exact False.elim (not_msame_b1_b0 h)
          · intro h
            exact False.elim (Bool.noConfusion h)
      | b1 =>
          constructor
          · intro _
            rfl
          · intro _
            exact msame_refl BMark.b1

theorem classifier_iff_endpoint_hsame_via_stdBridge (b c : CBool) :
    BoolClassifierSpec b c ↔
      BEDC.FKernel.Hist.hsame (BoolEndpoint b) (BoolEndpoint c) := by
  exact BEDC.Derived.BoolUp.BoolUp_StdBridge.right.left b c

def boolUpRelEquiv : BedcMathlibBridge.RelEquiv CBool BoolClassifierSpec Bool where
  toM := toBool
  ofM := ofBool
  leftInv := ofBool_toBool
  rightInv := toBool_ofBool
  relIff := classifier_iff_toBool_eq

def boolUpEquiv : CBool ≃ Bool :=
  boolUpRelEquiv.toEquiv

end BedcMathlibBridge.Constructive.Bool.BoolUp
