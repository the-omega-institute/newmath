import BEDC.Derived.RationalIntervalUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalPacket_consumer_readback_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint consumer readback :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory consumer ->
        Cont endpoint consumer readback ->
          PkgSig bundle readback pkg ->
            SemanticNameCert
              (fun row : BHist =>
                exists c : BHist, UnaryHistory c ∧ Cont endpoint c row ∧
                  PkgSig bundle row pkg)
              (fun row : BHist =>
                exists c : BHist, UnaryHistory c ∧ Cont endpoint c row)
              (fun row : BHist => PkgSig bundle row pkg)
              (fun row row' : BHist => psame bundle pkg pkg ∧ hsame row row') := by
  intro packet consumerUnary consumerReadbackRow readbackPkg
  obtain ⟨_leftUnary, _rightUnary, _orderUnary, _containmentUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, endpointUnary, _leftRightOrder,
    _orderContainmentTransport, _transportRouteProvenance, _provenanceNameEndpoint,
    _endpointPkg⟩ := packet
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed endpointUnary consumerUnary consumerReadbackRow
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro readback
          (Exists.intro consumer ⟨consumerUnary, consumerReadbackRow, readbackPkg⟩)
      equiv_refl := by
        intro row sourceRow
        obtain ⟨_c, _cUnary, _endpointCRow, rowPkg⟩ := sourceRow
        exact ⟨PkgSig_psame_intro rowPkg rowPkg (hsame_refl row), hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        exact ⟨classified.left, hsame_symm classified.right⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        obtain ⟨c, cUnary, endpointCRow, rowPkg⟩ := sourceRow
        cases classified.right
        exact Exists.intro c ⟨cUnary, endpointCRow, rowPkg⟩
    }
    pattern_sound := by
      intro _row sourceRow
      obtain ⟨c, cUnary, endpointCRow, _rowPkg⟩ := sourceRow
      exact Exists.intro c ⟨cUnary, endpointCRow⟩
    ledger_sound := by
      intro _row sourceRow
      obtain ⟨_c, _cUnary, _endpointCRow, rowPkg⟩ := sourceRow
      exact rowPkg
  }

end BEDC.Derived.RationalIntervalUp
