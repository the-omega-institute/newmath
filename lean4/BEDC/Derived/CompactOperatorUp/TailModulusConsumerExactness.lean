import BEDC.Derived.CompactOperatorUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CompactOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactOperatorTailModulusConsumerExactness [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName compactRead
      tailModulusRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.CompactOperatorCarrier source target operator imageNet modulus transport replay
        provenance localName bundle pkg ->
      Cont operator imageNet compactRead ->
        Cont compactRead modulus tailModulusRead ->
          Cont tailModulusRead replay consumerRead ->
            PkgSig bundle consumerRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row tailModulusRead ∨ hsame row consumerRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row target ∨ hsame row operator ∨
                      hsame row imageNet ∨ hsame row modulus ∨ hsame row compactRead ∨
                        hsame row tailModulusRead ∨ hsame row consumerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont operator imageNet compactRead ∧
                      Cont compactRead modulus tailModulusRead ∧
                        Cont tailModulusRead replay consumerRead ∧
                          PkgSig bundle consumerRead pkg)
                  hsame ∧ UnaryHistory compactRead ∧ UnaryHistory tailModulusRead ∧
                    UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: CompactOperatorCarrier BHist ProbeBundle Pkg Cont hsame
  intro carrier compactRoute tailModulusRoute consumerRoute consumerPkg
  obtain ⟨_sourceUnary, _targetUnary, operatorUnary, imageNetUnary, modulusUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localNameUnary, _sourceTargetOperator,
    _operatorImageNetModulus, _provenanceTransportLocalName, _localNamePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed operatorUnary imageNetUnary compactRoute
  have tailModulusUnary : UnaryHistory tailModulusRead :=
    unary_cont_closed compactUnary modulusUnary tailModulusRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed tailModulusUnary replayUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row tailModulusRead ∨ hsame row consumerRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row operator ∨
              hsame row imageNet ∨ hsame row modulus ∨ hsame row compactRead ∨
                hsame row tailModulusRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont operator imageNet compactRead ∧
              Cont compactRead modulus tailModulusRead ∧
                Cont tailModulusRead replay consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead
        ⟨Or.inr (hsame_refl consumerRead), consumerUnary⟩
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
        · cases source.left with
          | inl sameTail =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameTail)
          | inr sameConsumer =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameConsumer)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameTail =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameTail))))))
      | inr sameConsumer =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameConsumer))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactRoute, tailModulusRoute, consumerRoute, consumerPkg⟩
  }
  exact ⟨cert, compactUnary, tailModulusUnary, consumerUnary⟩

end BEDC.Derived.CompactOperatorUp
