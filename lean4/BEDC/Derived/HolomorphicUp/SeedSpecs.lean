import BEDC.Derived.HolomorphicUp.IteratedTransport

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def HolomorphicSourceSpec (center radius point : BHist) (gap : BHist) : Prop :=
  HolomorphicOpenDisk center radius point gap ∧
    HolomorphicOpenDiskWitnessed center radius point

theorem HolomorphicSourceSpec_semantic_name_certificate {center radius point gap : BHist} :
    HolomorphicSourceSpec center radius point gap ->
      SemanticNameCert (HolomorphicSourceSpec center radius point)
        (HolomorphicSourceSpec center radius point) (HolomorphicSourceSpec center radius point)
        hsame := by
  intro source
  constructor
  · constructor
    · exact Exists.intro gap source
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      have diskK : HolomorphicOpenDisk center radius point k :=
        (HolomorphicOpenDisk_hsame_transport (hsame_refl center) (hsame_refl radius)
          (hsame_refl point) same carrier.left).left
      exact And.intro diskK carrier.right
  · intro _h sourceH
    exact sourceH
  · intro _h sourceH
    exact sourceH

def HolomorphicClassifierSpec (center radius point : BHist) (h k : BHist) : Prop :=
  HolomorphicSourceSpec center radius point h ∧
    HolomorphicSourceSpec center radius point k ∧ hsame h k

theorem HolomorphicClassifierSpec_semantic_name_certificate {center radius point gap : BHist} :
    HolomorphicSourceSpec center radius point gap ->
      SemanticNameCert (HolomorphicSourceSpec center radius point)
        (HolomorphicSourceSpec center radius point) (HolomorphicSourceSpec center radius point)
        (HolomorphicClassifierSpec center radius point) := by
  intro source
  constructor
  · constructor
    · exact Exists.intro gap source
    · intro h carrier
      exact And.intro carrier (And.intro carrier (hsame_refl h))
    · intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    · intro h k r classifiedHK classifiedKR
      exact And.intro classifiedHK.left
        (And.intro classifiedKR.right.left
          (hsame_trans classifiedHK.right.right classifiedKR.right.right))
    · intro _h k classified _carrier
      exact classified.right.left
  · intro _h sourceH
    exact sourceH
  · intro _h sourceH
    exact sourceH

def HolomorphicPatternSpec (seed : BHist) (iterate : BHist) : Prop :=
  UnaryHistory seed ∧ IteratedCplxDiff seed 1 iterate

theorem HolomorphicPatternSpec_semantic_name_certificate {seed iterate : BHist} :
    HolomorphicPatternSpec seed iterate ->
      SemanticNameCert (HolomorphicPatternSpec seed) (HolomorphicPatternSpec seed)
        (HolomorphicPatternSpec seed) hsame := by
  intro pattern
  constructor
  · constructor
    · exact Exists.intro iterate pattern
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro carrier.left
        (IteratedCplxDiff_hsame_transport_unary_readback (hsame_refl seed) same
          carrier.right).left
  · intro _h source
    exact source
  · intro _h source
    exact source

end BEDC.Derived.HolomorphicUp
