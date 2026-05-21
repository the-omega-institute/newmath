import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# SliceCategoryUp finite carrier surface.
-/

namespace BEDC.Derived.SliceCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SliceCategoryCarrier [AskSetup] [PackageSetup]
    (base displayed arrow fiber transport route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  UnaryHistory base ∧ UnaryHistory displayed ∧ UnaryHistory arrow ∧ UnaryHistory fiber ∧
    UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      UnaryHistory localName ∧ Cont displayed arrow base ∧ Cont route provenance localName ∧
        PkgSig bundle localName pkg ∧ hsame transport arrow

theorem SliceCategoryCarrier_kernel_fiber_obligation [AskSetup] [PackageSetup]
    {base displayed arrow fiber transport route provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SliceCategoryCarrier base displayed arrow fiber transport route provenance localName bundle pkg ->
      PkgSig bundle base pkg ->
        UnaryHistory base ∧ UnaryHistory displayed ∧ UnaryHistory arrow ∧
          Cont displayed arrow base ∧ Cont route provenance localName ∧ hsame transport arrow ∧
            PkgSig bundle localName pkg ∧ PkgSig bundle base pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro carrier basePkg
  obtain ⟨baseUnary, displayedUnary, arrowUnary, _fiberUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, displayedArrowBase,
    routeProvenanceLocalName, localNamePkg, transportArrow⟩ := carrier
  exact
    ⟨baseUnary, displayedUnary, arrowUnary, displayedArrowBase, routeProvenanceLocalName,
      transportArrow, localNamePkg, basePkg⟩

theorem SliceCategoryCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {base displayed arrow fiber transport route provenance localName baseRead fiberRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SliceCategoryCarrier base displayed arrow fiber transport route provenance localName bundle pkg ->
      PkgSig bundle base pkg ->
        Cont base fiber baseRead ->
          Cont arrow route fiberRead ->
            SemanticNameCert
                (fun row : BHist => hsame row localName ∧ UnaryHistory row ∧
                  PkgSig bundle row pkg)
                (fun _row : BHist =>
                  UnaryHistory base ∧ UnaryHistory displayed ∧ UnaryHistory arrow ∧
                    Cont displayed arrow base)
                (fun row : BHist =>
                  PkgSig bundle row pkg ∧ Cont route provenance localName)
                (fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row') ∧
              UnaryHistory base ∧ UnaryHistory displayed ∧ UnaryHistory arrow ∧
                UnaryHistory fiber ∧ UnaryHistory baseRead ∧ UnaryHistory fiberRead ∧
                  Cont displayed arrow base ∧ Cont base fiber baseRead ∧
                    Cont arrow route fiberRead ∧ Cont route provenance localName ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle base pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro carrier basePkg baseRoute fiberRoute
  obtain ⟨baseUnary, displayedUnary, arrowUnary, fiberUnary, _transportUnary, _routeUnary,
    _provenanceUnary, localNameUnary, displayedArrowBase, routeProvenanceLocalName,
    localNamePkg, _transportArrow⟩ := carrier
  have baseReadUnary : UnaryHistory baseRead :=
    unary_cont_closed baseUnary fiberUnary baseRoute
  have fiberReadUnary : UnaryHistory fiberRead :=
    unary_cont_closed arrowUnary _routeUnary fiberRoute
  have sourceAtLocalName :
      hsame localName localName ∧ UnaryHistory localName ∧ PkgSig bundle localName pkg :=
    ⟨hsame_refl localName, localNameUnary, localNamePkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            UnaryHistory base ∧ UnaryHistory displayed ∧ UnaryHistory arrow ∧
              Cont displayed arrow base)
          (fun row : BHist => PkgSig bundle row pkg ∧ Cont route provenance localName)
          (fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row') := {
    core := {
      carrier_inhabited := Exists.intro localName sourceAtLocalName
      equiv_refl := by
        intro row source
        exact ⟨source.right.right, hsame_refl row⟩
      equiv_symm := by
        intro row other classified
        cases classified.right
        exact ⟨classified.left, hsame_refl row⟩
      equiv_trans := by
        intro _row _middle _other leftClassified rightClassified
        exact
          ⟨leftClassified.left,
            hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _other classified source
        cases classified.right
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left
      exact ⟨baseUnary, displayedUnary, arrowUnary, displayedArrowBase⟩
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨source.right.right, routeProvenanceLocalName⟩
  }
  exact
    ⟨cert, baseUnary, displayedUnary, arrowUnary, fiberUnary, baseReadUnary,
      fiberReadUnary, displayedArrowBase, baseRoute, fiberRoute, routeProvenanceLocalName,
      localNamePkg, basePkg⟩

end BEDC.Derived.SliceCategoryUp
