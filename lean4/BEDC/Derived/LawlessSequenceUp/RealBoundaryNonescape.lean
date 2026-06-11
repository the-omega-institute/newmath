import BEDC.Derived.LawlessSequenceUp.ChoiceFreeCarrierObligation
import BEDC.Derived.LawlessSequenceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LawlessSequenceRealBoundaryNonescape [AskSetup] [PackageSetup]
    {window boolDigits natIndex transport replay provenance localName streamRead namedRead
      realBoundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawless_sequence_stream_name_handoff_carrier
        window boolDigits natIndex transport replay provenance localName bundle pkg →
      Cont natIndex window streamRead →
        Cont streamRead boolDigits namedRead →
          Cont namedRead localName realBoundaryRead →
            PkgSig bundle realBoundaryRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row realBoundaryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row window ∨ hsame row boolDigits ∨ hsame row natIndex ∨
                      hsame row namedRead ∨ hsame row realBoundaryRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont natIndex window streamRead ∧
                      Cont streamRead boolDigits namedRead ∧
                        Cont namedRead localName realBoundaryRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle realBoundaryRead pkg)
                  hsame ∧
                UnaryHistory streamRead ∧ UnaryHistory namedRead ∧
                  UnaryHistory realBoundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows indexWindow streamDigit namedBoundary boundaryPkg
  obtain ⟨windowUnary, boolUnary, indexUnary, _transportUnary, _replayUnary,
    _provenanceUnary, localNameUnary, provenancePkg, _localNamePkg⟩ := carrierRows
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed indexUnary windowUnary indexWindow
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed streamUnary boolUnary streamDigit
  have boundaryUnary : UnaryHistory realBoundaryRead :=
    unary_cont_closed namedUnary localNameUnary namedBoundary
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro realBoundaryRead ⟨hsame_refl realBoundaryRead, boundaryUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, indexWindow, streamDigit, namedBoundary, provenancePkg, boundaryPkg⟩
    }
  · exact ⟨streamUnary, namedUnary, boundaryUnary⟩

end BEDC.Derived.LawlessSequenceUp
