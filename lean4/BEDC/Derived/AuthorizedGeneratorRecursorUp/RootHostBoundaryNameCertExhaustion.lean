import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootHostBoundaryNameCertExhaustion
    [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont gap name boundaryRead ->
      UnaryHistory gap ->
        UnaryHistory name ->
          PkgSig bundle provenance pkg ->
            authorizedGeneratorRecursorFromEventFlow
                (authorizedGeneratorRecursorToEventFlow
                  (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
                    audit transport routes provenance gap name)) =
              some
                (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent
                  output audit transport routes provenance gap name) ∧
              SemanticNameCert
                  (fun row : BHist => hsame row name ∧ UnaryHistory row)
                  (fun row : BHist => hsame row name ∧ Cont gap name boundaryRead)
                  (fun row : BHist =>
                    hsame row name ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro gapNameBoundary gapUnary nameUnary provenancePkg
  have roundTrip :
      authorizedGeneratorRecursorFromEventFlow
          (authorizedGeneratorRecursorToEventFlow
            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
              audit transport routes provenance gap name)) =
        some
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
            transport routes provenance gap name) := by
    have decodeEncode :
        ∀ h : BHist,
          authorizedGeneratorRecursorDecodeBHist (authorizedGeneratorRecursorEncodeBHist h) =
            h := by
      intro h
      induction h with
      | Empty =>
          rfl
      | e0 h ih =>
          exact congrArg BHist.e0 ih
      | e1 h ih =>
          exact congrArg BHist.e1 ih
    change
      some
        (AuthorizedGeneratorRecursorUp.mk
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist signature))
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist eliminator))
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist motive))
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist branches))
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist descent))
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist output))
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist audit))
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist transport))
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist routes))
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist provenance))
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist gap))
          (authorizedGeneratorRecursorDecodeBHist
            (authorizedGeneratorRecursorEncodeBHist name))) =
        some
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
            transport routes provenance gap name)
    rw [decodeEncode signature, decodeEncode eliminator, decodeEncode motive,
      decodeEncode branches, decodeEncode descent, decodeEncode output, decodeEncode audit,
      decodeEncode transport, decodeEncode routes, decodeEncode provenance, decodeEncode gap,
      decodeEncode name]
  have sourceName :
      (fun row : BHist => hsame row name ∧ UnaryHistory row) name := by
    exact ⟨hsame_refl name, nameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist => hsame row name ∧ Cont gap name boundaryRead)
          (fun row : BHist => hsame row name ∧ PkgSig bundle provenance pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro name sourceName
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    · intro row source
      exact ⟨source.left, gapNameBoundary⟩
    · intro row source
      exact ⟨source.left, provenancePkg⟩
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed gapUnary nameUnary gapNameBoundary
  exact ⟨roundTrip, cert, boundaryUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
