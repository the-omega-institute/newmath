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

theorem CompactOperatorFiniteRankApproximationBoundary [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName finiteRankRead
      approximationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.CompactOperatorCarrier source target operator imageNet modulus transport replay
        provenance localName bundle pkg ->
      Cont operator imageNet finiteRankRead ->
        Cont finiteRankRead modulus approximationRead ->
          PkgSig bundle approximationRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row approximationRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row target ∨ hsame row operator ∨
                    hsame row imageNet ∨ hsame row modulus ∨ hsame row finiteRankRead ∨
                      hsame row approximationRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont operator imageNet finiteRankRead ∧
                    Cont finiteRankRead modulus approximationRead ∧
                      PkgSig bundle approximationRead pkg)
                hsame ∧ UnaryHistory finiteRankRead ∧ UnaryHistory approximationRead := by
  -- BEDC touchpoint anchor: CompactOperatorCarrier BHist ProbeBundle Pkg Cont hsame
  intro carrier finiteRankRoute approximationRoute approximationPkg
  obtain ⟨_sourceUnary, _targetUnary, operatorUnary, imageNetUnary, modulusUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _sourceTargetOperator,
    _operatorImageNetModulus, _provenanceTransportLocalName, _localNamePkg⟩ := carrier
  have finiteRankUnary : UnaryHistory finiteRankRead :=
    unary_cont_closed operatorUnary imageNetUnary finiteRankRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed finiteRankUnary modulusUnary approximationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row approximationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row operator ∨
              hsame row imageNet ∨ hsame row modulus ∨ hsame row finiteRankRead ∨
                hsame row approximationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont operator imageNet finiteRankRead ∧
              Cont finiteRankRead modulus approximationRead ∧
                PkgSig bundle approximationRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro approximationRead ⟨hsame_refl approximationRead, approximationUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, finiteRankRoute, approximationRoute, approximationPkg⟩
  }
  exact ⟨cert, finiteRankUnary, approximationUnary⟩

end BEDC.Derived.CompactOperatorUp
