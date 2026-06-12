import BEDC.Derived.BetaSubstitutionPreservationUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BetaSubstitutionPreservationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem BetaSubstitutionPreservationNameCertObligations :
    SemanticNameCert
      (fun h : BHist =>
        betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist h) =
          h)
      (fun h : BHist =>
        hsame h
          (betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist h)))
      (fun h : BHist =>
        betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist h) =
          h)
      hsame := by
  -- BEDC touchpoint anchor: BHist BMark hsame SemanticNameCert
  have decodeEncode :
      ∀ h : BHist,
        betaSubstitutionPreservationDecodeBHist
            (betaSubstitutionPreservationEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (decodeEncode BHist.Empty)
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro _h _k same
        exact hsame_symm same
      equiv_trans := by
        intro _h _k _r sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _h k _same _source
        exact decodeEncode k
    }
    pattern_sound := by
      intro h source
      exact source.symm
    ledger_sound := by
      intro _h source
      exact source
  }

end BEDC.Derived.BetaSubstitutionPreservationUp
