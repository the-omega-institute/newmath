import BEDC.Derived.CompactOperatorUp.ApproximationScheme
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CompactOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactOperatorPublicExportStatus [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName compactRead
      approximationRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactOperatorApproximationScheme source target operator imageNet modulus transport replay
        provenance localName compactRead approximationRead bundle pkg →
      Cont approximationRead replay publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row target ∨ hsame row operator ∨
                  hsame row imageNet ∨ hsame row modulus ∨ hsame row transport ∨
                    hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                      hsame row compactRead ∨ hsame row approximationRead ∨
                        hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont operator imageNet compactRead ∧
                  Cont compactRead modulus approximationRead ∧
                    Cont approximationRead replay publicRead ∧ PkgSig bundle publicRead pkg)
              hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: CompactOperatorApproximationScheme BHist ProbeBundle Pkg Cont hsame
  intro scheme publicRoute publicPkg
  obtain ⟨carrier, compactRoute, approximationRoute, _approximationPkg⟩ := scheme
  obtain ⟨_sourceUnary, _targetUnary, operatorUnary, imageNetUnary, modulusUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localNameUnary, _sourceTargetOperator,
    _operatorImageNetModulus, _provenanceTransportLocalName, _localNamePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed operatorUnary imageNetUnary compactRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed compactUnary modulusUnary approximationRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed approximationUnary replayUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row operator ∨
              hsame row imageNet ∨ hsame row modulus ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row compactRead ∨ hsame row approximationRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont operator imageNet compactRead ∧
              Cont compactRead modulus approximationRead ∧
                Cont approximationRead replay publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactRoute, approximationRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.CompactOperatorUp
