import BEDC.Derived.CompactOperatorUp.FiniteRankApproximationBoundary
import BEDC.Derived.CompactOperatorUp.TailModulusConsumerExactness

namespace BEDC.Derived.CompactOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactOperatorObligationScope [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName compactRead
      tailModulusRead finiteRankRead approximationRead spectralRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.CompactOperatorCarrier source target operator imageNet modulus transport replay
        provenance localName bundle pkg →
      Cont operator imageNet compactRead →
        Cont compactRead modulus tailModulusRead →
          Cont compactRead modulus finiteRankRead →
            Cont finiteRankRead modulus approximationRead →
              Cont provenance replay spectralRead →
                Cont tailModulusRead approximationRead scopeRead →
                  PkgSig bundle scopeRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row source ∨ hsame row target ∨ hsame row operator ∨
                            hsame row imageNet ∨ hsame row modulus ∨ hsame row compactRead ∨
                              hsame row tailModulusRead ∨ hsame row finiteRankRead ∨
                                hsame row approximationRead ∨ hsame row spectralRead ∨
                                  hsame row scopeRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont operator imageNet compactRead ∧
                            Cont compactRead modulus tailModulusRead ∧
                              Cont compactRead modulus finiteRankRead ∧
                                Cont finiteRankRead modulus approximationRead ∧
                                  Cont provenance replay spectralRead ∧
                                    Cont tailModulusRead approximationRead scopeRead ∧
                                      PkgSig bundle scopeRead pkg)
                        hsame ∧
                      UnaryHistory compactRead ∧ UnaryHistory tailModulusRead ∧
                        UnaryHistory finiteRankRead ∧ UnaryHistory approximationRead ∧
                          UnaryHistory spectralRead ∧ UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: CompactOperatorCarrier BHist ProbeBundle Pkg Cont hsame
  intro carrier compactRoute tailModulusRoute finiteRankRoute approximationRoute spectralRoute
    scopeRoute scopePkg
  obtain ⟨_sourceUnary, _targetUnary, operatorUnary, imageNetUnary, modulusUnary,
    _transportUnary, replayUnary, provenanceUnary, _localNameUnary, _sourceTargetOperator,
    _operatorImageNetModulus, _provenanceTransportLocalName, _localNamePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed operatorUnary imageNetUnary compactRoute
  have tailModulusUnary : UnaryHistory tailModulusRead :=
    unary_cont_closed compactUnary modulusUnary tailModulusRoute
  have finiteRankUnary : UnaryHistory finiteRankRead :=
    unary_cont_closed compactUnary modulusUnary finiteRankRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed finiteRankUnary modulusUnary approximationRoute
  have spectralUnary : UnaryHistory spectralRead :=
    unary_cont_closed provenanceUnary replayUnary spectralRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed tailModulusUnary approximationUnary scopeRoute
  have sourceScope :
      (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row) scopeRead := by
    exact ⟨hsame_refl scopeRead, scopeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row operator ∨
              hsame row imageNet ∨ hsame row modulus ∨ hsame row compactRead ∨
                hsame row tailModulusRead ∨ hsame row finiteRankRead ∨
                  hsame row approximationRead ∨ hsame row spectralRead ∨ hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont operator imageNet compactRead ∧
              Cont compactRead modulus tailModulusRead ∧
                Cont compactRead modulus finiteRankRead ∧
                  Cont finiteRankRead modulus approximationRead ∧
                    Cont provenance replay spectralRead ∧
                      Cont tailModulusRead approximationRead scopeRead ∧
                        PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead sourceScope
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactRoute, tailModulusRoute, finiteRankRoute,
          approximationRoute, spectralRoute, scopeRoute, scopePkg⟩
  }
  exact
    ⟨cert, compactUnary, tailModulusUnary, finiteRankUnary, approximationUnary, spectralUnary,
      scopeUnary⟩

end BEDC.Derived.CompactOperatorUp
