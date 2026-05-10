import BEDC.Derived.ChernWeilUp

namespace BEDC.Derived.ChernWeilUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ChernWeilNameCert_obligation_surface
    {curvature derham provenance connectionFace characteristic : BHist} :
    ChernWeilSourceEnvelope curvature derham provenance connectionFace characteristic ->
      SemanticNameCert
        (fun h : BHist =>
          ChernWeilSourceEnvelope curvature derham provenance connectionFace h)
        (fun h : BHist =>
          ChernWeilSourceEnvelope curvature derham provenance connectionFace h)
        (fun h : BHist =>
          ChernWeilSourceEnvelope curvature derham provenance connectionFace h)
        (fun left right : BHist =>
          ChernWeilSourceEnvelope curvature derham provenance connectionFace left ∧
            ChernWeilSourceEnvelope curvature derham provenance connectionFace right ∧
              hsame left right) := by
  intro envelope
  constructor
  · constructor
    · exact Exists.intro characteristic envelope
    · intro h source
      exact And.intro source (And.intro source (hsame_refl h))
    · intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    · intro h k r classifiedHK classifiedKR
      exact And.intro classifiedHK.left
        (And.intro classifiedKR.right.left
          (hsame_trans classifiedHK.right.right classifiedKR.right.right))
    · intro h k classified _source
      exact classified.right.left
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.ChernWeilUp
