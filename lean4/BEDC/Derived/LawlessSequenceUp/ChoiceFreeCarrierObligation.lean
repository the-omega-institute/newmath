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

theorem LawlessSequenceChoiceFreeCarrierObligation [AskSetup] [PackageSetup]
    {window boolDigits natIndex transport replay provenance localName streamRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawless_sequence_stream_name_handoff_carrier
        window boolDigits natIndex transport replay provenance localName
        bundle pkg →
      Cont natIndex window streamRead →
        Cont streamRead boolDigits namedRead →
          PkgSig bundle namedRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  lawless_sequence_stream_name_handoff_carrier
                    window boolDigits natIndex transport replay provenance
                    localName bundle pkg ∧ (hsame row streamRead ∨ hsame row namedRead))
                (fun row : BHist =>
                  hsame row window ∨ hsame row boolDigits ∨ hsame row natIndex ∨
                    hsame row streamRead ∨ hsame row namedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle namedRead pkg)
                hsame ∧
              UnaryHistory streamRead ∧ UnaryHistory namedRead ∧
                Cont natIndex window streamRead ∧ Cont streamRead boolDigits namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows indexWindow streamDigit namedPkg
  obtain ⟨windowUnary, boolUnary, indexUnary, transportUnary, replayUnary,
    provenanceUnary, localNameUnary, provenancePkg, localNamePkg⟩ := carrierRows
  have carrierWitness :
      lawless_sequence_stream_name_handoff_carrier
        window boolDigits natIndex transport replay provenance
        localName bundle pkg := by
    exact
      ⟨windowUnary, boolUnary, indexUnary, transportUnary, replayUnary, provenanceUnary,
        localNameUnary, provenancePkg, localNamePkg⟩
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed indexUnary windowUnary indexWindow
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed streamUnary boolUnary streamDigit
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            lawless_sequence_stream_name_handoff_carrier
              window boolDigits natIndex transport replay provenance
              localName bundle pkg ∧ (hsame row streamRead ∨ hsame row namedRead))
          (fun row : BHist =>
            hsame row window ∨ hsame row boolDigits ∨ hsame row natIndex ∨
              hsame row streamRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨carrierWitness, Or.inr (hsame_refl namedRead)⟩
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
        constructor
        · exact source.left
        · cases source.right with
          | inl rowStream =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) rowStream)
          | inr rowNamed =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) rowNamed)
    }
    pattern_sound := by
      intro _row source
      cases source.right with
      | inl rowStream =>
          exact Or.inr (Or.inr (Or.inr (Or.inl rowStream)))
      | inr rowNamed =>
          exact Or.inr (Or.inr (Or.inr (Or.inr rowNamed)))
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row := by
        cases source.right with
        | inl rowStream =>
            exact unary_transport streamUnary (hsame_symm rowStream)
        | inr rowNamed =>
            exact unary_transport namedUnary (hsame_symm rowNamed)
      exact ⟨rowUnary, provenancePkg, localNamePkg, namedPkg⟩
  }
  exact ⟨cert, streamUnary, namedUnary, indexWindow, streamDigit⟩

end BEDC.Derived.LawlessSequenceUp
