import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberSelectedTailRadiusAdmission [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailAdmission streamTail
      regularTail toleranceTail realTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont window radius tailAdmission →
        Cont tailAdmission mesh streamTail →
          Cont streamTail route regularTail →
            Cont regularTail transport toleranceTail →
              Cont toleranceTail nameRow realTail →
                PkgSig bundle realTail pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row realTail ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row tailAdmission ∨ hsame row streamTail ∨
                          hsame row regularTail ∨ hsame row toleranceTail ∨
                            hsame row realTail)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle realTail pkg ∧
                          hsame row realTail)
                      hsame ∧
                    UnaryHistory tailAdmission ∧ UnaryHistory streamTail ∧
                      UnaryHistory regularTail ∧ UnaryHistory toleranceTail ∧
                        UnaryHistory realTail ∧ Cont window radius tailAdmission ∧
                          Cont tailAdmission mesh streamTail ∧
                            Cont streamTail route regularTail ∧
                              Cont regularTail transport toleranceTail ∧
                                Cont toleranceTail nameRow realTail ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle realTail pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert hsame
  intro carrier windowRadiusTail tailMeshStream streamRouteRegular regularTransportTolerance
    toleranceNameReal realPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
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
  have sourceReal :
      (fun row : BHist => hsame row realTail ∧ UnaryHistory row) realTail := by
    exact ⟨hsame_refl realTail, realUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realTail ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row tailAdmission ∨ hsame row streamTail ∨ hsame row regularTail ∨
            hsame row toleranceTail ∨ hsame row realTail)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle realTail pkg ∧ hsame row realTail)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realTail sourceReal
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, realPkg, source.left⟩
    }
  exact
    ⟨cert, tailUnary, streamUnary, regularUnary, toleranceUnary, realUnary,
      windowRadiusTail, tailMeshStream, streamRouteRegular, regularTransportTolerance,
      toleranceNameReal, provenancePkg, realPkg⟩

theorem FiniteLebesgueNumberTotalBoundedRadiusSourceLock [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailAdmission streamTail
      regularTail toleranceTail realTail totalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont window radius tailAdmission →
        Cont tailAdmission mesh streamTail →
          Cont streamTail route regularTail →
            Cont regularTail transport toleranceTail →
              Cont toleranceTail nameRow realTail →
                Cont realTail provenance totalRead →
                  PkgSig bundle realTail pkg →
                    PkgSig bundle totalRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row totalRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row tailAdmission ∨ hsame row streamTail ∨
                              hsame row regularTail ∨ hsame row toleranceTail ∨
                                hsame row realTail ∨ hsame row totalRead)
                          (fun row : BHist =>
                            PkgSig bundle provenance pkg ∧ PkgSig bundle totalRead pkg ∧
                              hsame row totalRead)
                          hsame ∧
                        UnaryHistory tailAdmission ∧ UnaryHistory streamTail ∧
                          UnaryHistory regularTail ∧ UnaryHistory toleranceTail ∧
                            UnaryHistory realTail ∧ UnaryHistory totalRead ∧
                              Cont window radius tailAdmission ∧
                                Cont tailAdmission mesh streamTail ∧
                                  Cont streamTail route regularTail ∧
                                    Cont regularTail transport toleranceTail ∧
                                      Cont toleranceTail nameRow realTail ∧
                                        Cont realTail provenance totalRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle totalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert hsame
  intro carrier windowRadiusTail tailMeshStream streamRouteRegular regularTransportTolerance
    toleranceNameReal realProvenanceTotal _realPkg totalPkg
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
            hsame row toleranceTail ∨ hsame row realTail ∨ hsame row totalRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle totalRead pkg ∧ hsame row totalRead)
        hsame := by
    exact {
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, totalPkg, source.left⟩
    }
  exact
    ⟨cert, tailUnary, streamUnary, regularUnary, toleranceUnary, realUnary, totalUnary,
      windowRadiusTail, tailMeshStream, streamRouteRegular, regularTransportTolerance,
      toleranceNameReal, realProvenanceTotal, provenancePkg, totalPkg⟩

theorem FiniteLebesgueNumberSelectedTailUniformConsumerRoute [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailAdmission streamTail
      regularTail toleranceTail realTail uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont window radius tailAdmission →
        Cont tailAdmission mesh streamTail →
          Cont streamTail route regularTail →
            Cont regularTail transport toleranceTail →
              Cont toleranceTail nameRow realTail →
                Cont realTail mesh uniformRead →
                  PkgSig bundle uniformRead pkg →
                    UnaryHistory realTail ∧ UnaryHistory uniformRead ∧
                      Cont toleranceTail nameRow realTail ∧ Cont realTail mesh uniformRead ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier windowRadiusTail tailMeshStream streamRouteRegular regularTransportTolerance
    toleranceNameReal realMeshUniform uniformPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
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
  exact
    ⟨realUnary, uniformUnary, toleranceNameReal, realMeshUniform, provenancePkg,
      uniformPkg⟩

def FiniteLebesgueNumberSelectedTailBridgeLedger [AskSetup] [PackageSetup]
    (cover window radius mesh transport route provenance nameRow tailAdmission streamTail
      regularTail toleranceTail realTail : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
      bundle pkg ∧
    Cont window radius tailAdmission ∧ Cont tailAdmission mesh streamTail ∧
      Cont streamTail route regularTail ∧ Cont regularTail transport toleranceTail ∧
        Cont toleranceTail nameRow realTail ∧ PkgSig bundle realTail pkg

theorem FiniteLebesgueNumberSelectedTailBridgeLedger_certificate [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailAdmission streamTail
      regularTail toleranceTail realTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberSelectedTailBridgeLedger cover window radius mesh transport route
        provenance nameRow tailAdmission streamTail regularTail toleranceTail realTail bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row realTail ∧
              FiniteLebesgueNumberSelectedTailBridgeLedger cover window radius mesh transport
                route provenance nameRow tailAdmission streamTail regularTail toleranceTail
                realTail bundle pkg)
          (fun row : BHist =>
            hsame row tailAdmission ∨ hsame row streamTail ∨ hsame row regularTail ∨
              hsame row toleranceTail ∨ hsame row realTail)
          (fun row : BHist => hsame row realTail ∧ PkgSig bundle realTail pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro ledger
  have ledgerPacket :
      FiniteLebesgueNumberSelectedTailBridgeLedger cover window radius mesh transport route
        provenance nameRow tailAdmission streamTail regularTail toleranceTail realTail bundle
        pkg :=
    ledger
  obtain ⟨_carrier, _windowRadiusTail, _tailMeshStream, _streamRouteRegular,
    _regularTransportTolerance, _toleranceNameReal, realPkg⟩ := ledger
  have sourceReal :
      (fun row : BHist =>
        hsame row realTail ∧
          FiniteLebesgueNumberSelectedTailBridgeLedger cover window radius mesh transport route
            provenance nameRow tailAdmission streamTail regularTail toleranceTail realTail
            bundle pkg) realTail := by
    exact ⟨hsame_refl realTail, ledgerPacket⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro realTail sourceReal
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, realPkg⟩
  }

end BEDC.Derived.FiniteLebesgueNumberUp
