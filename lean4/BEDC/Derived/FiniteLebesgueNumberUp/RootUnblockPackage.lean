import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRootUnblockPackage [AskSetup] [PackageSetup]
    {cover window radius mesh stream regular real compact compactNet transport route provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover radius stream ->
        Cont stream mesh regular ->
          Cont regular compact real ->
            Cont real compactNet nameRow ->
              PkgSig bundle real pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row real ∧
                        FiniteLebesgueNumberCarrier cover window radius mesh transport route
                          provenance nameRow bundle pkg)
                    (fun row : BHist =>
                      hsame row real ∧ Cont cover radius stream ∧
                        Cont stream mesh regular ∧ Cont regular compact real ∧
                          Cont real compactNet nameRow)
                    (fun row : BHist => hsame row real ∧ PkgSig bundle real pkg)
                    hsame ∧
                  UnaryHistory stream ∧ UnaryHistory regular ∧ UnaryHistory real ∧
                    Cont cover radius stream ∧ Cont stream mesh regular ∧
                      Cont regular compact real ∧ Cont real compactNet nameRow ∧
                        PkgSig bundle real pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier coverRadiusStream streamMeshRegular regularCompactReal realCompactNetName realPkg
  have carrierPacket :
      FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute, _routeNameProvenance,
    _provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory stream :=
    unary_cont_closed coverUnary radiusUnary coverRadiusStream
  have regularUnary : UnaryHistory regular :=
    unary_cont_closed streamUnary meshUnary streamMeshRegular
  have realUnary : UnaryHistory real :=
    unary_cont_left_factor realCompactNetName nameRowUnary
  have sourceReal :
      (fun row : BHist =>
        hsame row real ∧
          FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
            bundle pkg) real := by
    exact ⟨hsame_refl real, carrierPacket⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row real ∧
            FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
              bundle pkg)
        (fun row : BHist =>
          hsame row real ∧ Cont cover radius stream ∧ Cont stream mesh regular ∧
            Cont regular compact real ∧ Cont real compactNet nameRow)
        (fun row : BHist => hsame row real ∧ PkgSig bundle real pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro real sourceReal
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
      exact
        ⟨source.left, coverRadiusStream, streamMeshRegular, regularCompactReal,
          realCompactNetName⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, realPkg⟩
  }
  exact
    ⟨cert, streamUnary, regularUnary, realUnary, coverRadiusStream, streamMeshRegular,
      regularCompactReal, realCompactNetName, realPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
