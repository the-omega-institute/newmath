import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberSelectedTailModulusExhaustion [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailAdmission streamTail
      regularTail toleranceTail realTail uniformRead totalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont window radius tailAdmission →
        Cont tailAdmission mesh streamTail →
          Cont streamTail route regularTail →
            Cont regularTail transport toleranceTail →
              Cont toleranceTail nameRow realTail →
                Cont realTail mesh uniformRead →
                  Cont realTail provenance totalRead →
                    PkgSig bundle uniformRead pkg →
                      PkgSig bundle totalRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row totalRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row tailAdmission ∨ hsame row streamTail ∨
                                hsame row regularTail ∨ hsame row toleranceTail ∨
                                  hsame row realTail ∨ hsame row uniformRead ∨
                                    hsame row totalRead)
                            (fun row : BHist =>
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle uniformRead pkg ∧
                                  PkgSig bundle totalRead pkg ∧ hsame row totalRead)
                            hsame ∧
                          UnaryHistory tailAdmission ∧ UnaryHistory streamTail ∧
                            UnaryHistory regularTail ∧ UnaryHistory toleranceTail ∧
                              UnaryHistory realTail ∧ UnaryHistory uniformRead ∧
                                UnaryHistory totalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowRadiusTail tailMeshStream streamRouteRegular regularTransportTolerance
    toleranceNameReal realMeshUniform realProvenanceTotal uniformPkg totalPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailAdmission :=
    unary_cont_closed windowUnary radiusUnary windowRadiusTail
  have streamUnary : UnaryHistory streamTail :=
    unary_cont_closed tailUnary meshUnary tailMeshStream
  have regularUnary : UnaryHistory regularTail :=
    unary_cont_closed streamUnary routeUnary streamRouteRegular
  have toleranceUnary : UnaryHistory toleranceTail :=
    unary_cont_closed regularUnary transportUnary regularTransportTolerance
  have realUnary : UnaryHistory realTail :=
    unary_cont_closed toleranceUnary nameRowUnary toleranceNameReal
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed realUnary meshUnary realMeshUniform
  have totalUnary : UnaryHistory totalRead :=
    unary_cont_closed realUnary provenanceUnary realProvenanceTotal
  have sourceTotal :
      (fun row : BHist => hsame row totalRead ∧ UnaryHistory row) totalRead := by
    exact ⟨hsame_refl totalRead, totalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row totalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailAdmission ∨ hsame row streamTail ∨ hsame row regularTail ∨
              hsame row toleranceTail ∨ hsame row realTail ∨ hsame row uniformRead ∨
                hsame row totalRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
              PkgSig bundle totalRead pkg ∧ hsame row totalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro totalRead sourceTotal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, uniformPkg, totalPkg, source.left⟩
  }
  exact
    ⟨cert, tailUnary, streamUnary, regularUnary, toleranceUnary, realUnary, uniformUnary,
      totalUnary⟩

end BEDC.Derived.FiniteLebesgueNumberUp
